(**************************************************************************)
(*                                                                        *)
(*  Copyright (c) 2025 OCamlPro SAS                                       *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  This file is distributed under the terms of the GNU Lesser General    *)
(*  Public License version 2.1, with the special exception on linking     *)
(*  described in the LICENSE.md file in the root directory.               *)
(*                                                                        *)
(*                                                                        *)
(**************************************************************************)

open Yalo.V1
open Yalo_plugin_ocaml.V1

open OCAML_AST

type 'a warning_config = {
  w_string_concat : 'a ;
  w_incr_decr : 'a ;
  w_comp_boolean : 'a ;
  w_failwith_sprintf : 'a ;
  w_list_length_comp_zero : 'a ;
  w_list_length_comp_list_length : 'a ;
  w_list_length_comp_any : 'a ;
  w_then_bool_else_bool : 'a ;
  w_then_or_else_bool : 'a ;
  w_else_unit : 'a ;
  w_try_catch_all : 'a ;
  w_list_append_for_one : 'a ;
  w_useless_sprintf : 'a ;
  w_suspicious_for_zero_to_len : 'a ;
  w_fun_fun : 'a ;
}

let w_string_concat = YALO.mkdesc ~name:"string_concat"
    {|(a ^ b ^ c) should be replaced by Printf.sprintf "%s%s%s" a b c|}
    ~what_it_does:"Checks for the concatenation of more than 2 strings using ^"
    ~why_restrict_this:
      "There is a performance issue to using the (^) operator multiple \
       times in the same expression, as it will allocate a new string \
       at every call. Instead, you can use `Printf.sprintf \"%s%s%s\"` \
       that will only allocate for the result once."
    ~example:
      "```\nlet s = a ^ \".\" ^ b\n```\n should be replaced by \
       \n```\nlet s = Printf.sprintf \"%s.%s\" a b\n```\n"
let w_incr_decr = YALO.mkdesc ~name:"incr_decr"
    {|"x := !x +/- 1" should be replaced by "incr/decr x"|}
let w_comp_boolean = YALO.mkdesc ~name:"comp_boolean"
    {|comparison with a boolean should always be simplified|}
let w_failwith_sprintf = YALO.mkdesc ~name:"failwith_sprintf"
    "\"failwith (sprintf [...])\" should be replaced by \
     \"Printf.ksprintf failwith [...]\""
let w_list_length_comp_zero = YALO.mkdesc ~name:"list_length_comp_zero"
    {|"String.length l =/<> 0" should be replaced by "l =/<> []"|}
let  w_list_length_comp_any = YALO.mkdesc ~name:"list_length_comp_any"
    {|"String.length l <=> _" should be replaced by "List.compare_length_with \
l =/<=> _"|}
let w_list_length_comp_list_length =
  YALO.mkdesc ~name:"list_length_comp_list_length"
    {|"String.length l1 <=> List.length l2" should be replaced by \
"List.compare_lengths l1 l2 <=> 0"|}
let w_then_bool_else_bool = YALO.mkdesc ~name:"then_bool_else_bool"
    {|"if then bool else bool" should be simplified|}
let w_then_or_else_bool = YALO.mkdesc ~name:"then_or_else_bool"
    {|bool in then/else should be simplified with && or |||}
let w_else_unit = YALO.mkdesc ~name:"else_unit"
    {|"else unit" is useless here|}
let w_try_catch_all = YALO.mkdesc ~name:"try_catch_all"
    {|"try with _" is dangerous, raised exceptions should be used or printed|}
let w_list_append_for_one = YALO.mkdesc ~name:"list_append_for_one"
    {|"[e]@list" should be replaced by "e :: list"|}
let w_useless_sprintf = YALO.mkdesc ~name:"useless_sprintf"
    {|'Printf.sprintf "%s"' is identify for string|}
let w_suspicious_for_zero_to_len = YALO.mkdesc
    ~name: "suspicious_for_zero_to_len"
    {|'for 0 to len do' is suspicious, should be 'len-1'|}
let w_fun_fun = YALO.mkdesc ~name:"fun_fun"
    {|All arguments of an immediate fun should be defined at once|}

let msg = {
  w_string_concat ;
  w_incr_decr ;
  w_comp_boolean ;
  w_failwith_sprintf ;
  w_list_length_comp_zero ;
  w_list_length_comp_any ;
  w_list_length_comp_list_length ;
  w_then_bool_else_bool ;
  w_then_or_else_bool ;
  w_else_unit ;
  w_try_catch_all ;
  w_list_append_for_one ;
  w_useless_sprintf ;
  w_suspicious_for_zero_to_len ;
  w_fun_fun ;
}

let no_nested_ifthenelse () =
  List.for_all (function
      | OCAML_AST.OCAML_TRAVERSE.Node_expression {
          pexp_desc = Pexp_ifthenelse _ ; _} -> false
      | _ -> true) (OCAML_AST.OCAML_TRAVERSE.node_stack ())


let rec catch_all cases =
  match cases with
  | [] -> false
  | { pc_lhs = { ppat_desc = Ppat_any; _ };
      pc_guard = None ; _ } :: _ -> true
  | _ :: cases -> catch_all cases


[%%if ocaml_version < (5,1,0)]
let check_fun_fun e =
  match e.pexp_desc with
    Pexp_fun (_, _, _, { pexp_desc = Pexp_function _ ; _ }) ->
      true
  | Pexp_fun (_, _, _, { pexp_desc = Pexp_fun _ ; pexp_loc ;_ }) ->
      not pexp_loc.loc_ghost
  | _ -> false
[%%else]
let check_fun_fun e =
  match e.pexp_desc with
  | Pexp_function (_ :: _, _,
                   Pfunction_body
                     { pexp_desc = Pexp_function _ ;
                       pexp_loc ; _ ;
                     })
    when e.pexp_loc.loc_ghost && not pexp_loc.loc_ghost
    -> true
  | _ -> false
[%%endif]


(* to prevent some patterns from hiding other warnings, find_warning
   returns a new config without the warning it has found, so that it
   can be called multiple times *)
let find_warning config e =
  match config, e.pexp_desc with

  (* detect ( _ ^ _ ^ _ ) *)
  | { w_string_concat = Some w ; _},
    Pexp_apply(
      { pexp_desc = Pexp_ident { txt = Lident "^"; _ } ; _ },
      [ _, _ ;
        _,
        { pexp_desc = Pexp_apply (
              { pexp_desc = Pexp_ident { txt = Lident "^" ; _ } ; _ },
              _ ) ; _ } ]
    ) ->
      Some (w, None, { config with w_string_concat = None })

  (* detect x := !x + 1 ---> incr x *)
  |  { w_incr_decr = Some w ; _},
     Pexp_apply (
       { pexp_desc = Pexp_ident { txt = Lident ":=";_};_},
       [
         Nolabel,
         { pexp_desc = Pexp_ident var1;_} ;
         Nolabel,
         { pexp_desc = Pexp_apply (
               { pexp_desc = Pexp_ident
                     { txt = Lident (( "+" | "-") as op);_};_},
               (
                 [
                   Nolabel,
                   { pexp_desc = Pexp_apply (
                         { pexp_desc = Pexp_ident
                               { txt = Lident "!";_};_},
                         [
                           Nolabel,
                           { pexp_desc = Pexp_ident var2;_} ]
                       );_};
                   Nolabel,
                   { pexp_desc =
                       Pexp_constant
                         (Pconst_integer ("1", None));_}
                 ]
               |
                 [
                   Nolabel,
                   { pexp_desc =
                       Pexp_constant
                         (Pconst_integer ("1", None));_};
                   Nolabel,
                   { pexp_desc = Pexp_apply (
                         { pexp_desc = Pexp_ident
                               { txt = Lident "!";_};_},
                         [
                           Nolabel,
                           { pexp_desc = Pexp_ident var2;_} ]
                       );_};
                 ]
               ));_}
       ]) when var1.txt = var2.txt ->
      let msg = Printf.sprintf
          {|"x := !x %s 1" should be replaced by "%s x"|}
          op (if op = "+" then "incr" else "decr")
      in
      Some (w, Some msg, { config with w_incr_decr = None })

  | { w_comp_boolean = Some w ; _},
    Pexp_apply (
      { pexp_desc =
          Pexp_ident {
            txt = Lident ( "=" | "<>" | "==" | "!=" );_};_},
      (
        [
          Nolabel, _ ;
          Nolabel,
          { pexp_desc =
              Pexp_construct ({ txt = Lident ("false"|"true");_},_);_}
        ]
      | [
        Nolabel,
        { pexp_desc =
            Pexp_construct ({ txt = Lident ("false"|"true");_},_);_};
        Nolabel, _ ;
      ])) ->
      Some (w, None, { config with w_comp_boolean = None })

  | { w_failwith_sprintf = Some w ; _},
    Pexp_apply (
      { pexp_desc =
          Pexp_ident {
            txt = Lident "failwith" ;_};_},
      [
        Nolabel,
        { pexp_desc = Pexp_apply (
              { pexp_desc = Pexp_ident
                    { txt = lid; _};_},
              _ );_}
      ]) when OCAML_AST.longident_name lid = "Printf.sprintf" ->
      Some (w, None, { config with w_failwith_sprintf = None })

  | { w_list_length_comp_zero = Some w ; _},
    Pexp_apply (
      { pexp_desc =
          Pexp_ident {
            txt = Lident ( "=" | "<>" | "==" | "!=" | ">" ) ;_};_},
      [
        Nolabel,
        { pexp_desc =
            Pexp_apply (
              { pexp_desc = Pexp_ident
                    { txt = lid_list_length;_}; _},
              _);_} ;
        Nolabel,
        { pexp_desc =
            Pexp_constant
              (Pconst_integer ("0", None));_};
      ])
    when
      OCAML_AST.longident_name lid_list_length = "List.length" ->
      Some (w, None, { config with
                       w_list_length_comp_zero = None;
                       w_list_length_comp_any = None; })

  | { w_list_length_comp_list_length = Some w ; _},
    Pexp_apply (
      { pexp_desc =
          Pexp_ident {
            txt = Lident ( "=" | "<>" | "==" | "!="
                         | ">" | ">=" | "<" | "<=" ) ;_};_},
      [
        Nolabel,
        { pexp_desc =
            Pexp_apply (
              { pexp_desc = Pexp_ident
                    { txt = lid_list_length;_}; _},
              _);_} ;
        Nolabel,
        { pexp_desc =
            Pexp_apply (
              { pexp_desc = Pexp_ident
                    { txt = lid_list_length2;_}; _},
              _);_}
      ])
    when
      OCAML_AST.longident_name lid_list_length = "List.length"
      && OCAML_AST.longident_name lid_list_length2 = "List.length"
    ->
      Some (w, None, { config with w_list_length_comp_list_length = None;
                                   w_list_length_comp_any = None;
                     })

  | { w_list_length_comp_any = Some w ; _},
    Pexp_apply (
      { pexp_desc =
          Pexp_ident {
            txt = Lident ( "=" | "<>" | "==" | "!="
                         | ">" | ">=" | "<" | "<=" ) ;_};_},
      [
        Nolabel,
        { pexp_desc =
            Pexp_apply (
              { pexp_desc = Pexp_ident
                    { txt = lid_list_length;_}; _},
              _);_} ;
        Nolabel, _
      ])
    when
      OCAML_AST.longident_name lid_list_length = "List.length" ->
      Some (w, None, { config with w_list_length_comp_any = None; })

  | { w_then_bool_else_bool = Some w ; _},
    Pexp_ifthenelse (_,
                     { pexp_desc =
                         Pexp_construct ({ txt = Lident ("false"|"true");_},_);
                       _},
                     Some
                       { pexp_desc =
                           Pexp_construct (
                             { txt = Lident ("false"|"true");_},_);_})
    ->
      Some (w, None, { config with w_then_bool_else_bool = None;
                                   w_then_or_else_bool = None })

  | { w_then_or_else_bool = Some w ; _},
    (
      Pexp_ifthenelse (_, _,
                       Some
                         { pexp_desc =
                             Pexp_construct (
                               { txt = Lident ("false"|"true");_},_);_})
    |
      Pexp_ifthenelse (_,
                       { pexp_desc =
                           Pexp_construct ({ txt =
                                               Lident ("false"|"true");_},_);
                         _},
                       _
                      ))
    ->
      Some (w, None, { config with w_then_or_else_bool = None; })

  | { w_else_unit = Some w ; _},
    (
      Pexp_ifthenelse (_, _,
                       Some
                         { pexp_desc =
                             Pexp_construct (
                               { txt = Lident "()";_},_);_})
    )
    when no_nested_ifthenelse ()
    ->
      Some (w, None, { config with w_else_unit = None; })

  | { w_try_catch_all = Some w ; _},
    Pexp_try (_, cases)
    when catch_all cases
    ->
      Some (w, None, { config with w_try_catch_all = None; })

  | { w_list_append_for_one = Some w ; _},
    Pexp_apply (
      { pexp_desc = Pexp_ident { txt = Lident "@";_};_},
      [
        Nolabel,
        { pexp_desc =
            Pexp_construct (
              { txt = Lident "::";_},
              Some
                { pexp_desc = Pexp_tuple
                      [
                        _;
                        { pexp_desc =
                            Pexp_construct (
                              { txt = Lident "[]";_},
                              None);_}
                      ];_}
            );_};
        Nolabel,_
      ])
    ->
      Some (w, None, { config with w_list_append_for_one = None; })

  | { w_useless_sprintf = Some w ; _ },
    Pexp_apply (
      { pexp_desc = Pexp_ident { txt = printf_sprintf ; _};_},
      (
        Nolabel,
        { pexp_desc = Pexp_constant(
              Pconst_string("%s",_,_));_})::
      _)
    when OCAML_AST.longident_name printf_sprintf = "Printf.sprintf"
    ->
      Some (w, None, { config with w_useless_sprintf = None; })

  | { w_useless_sprintf = Some w ; _ },
    Pexp_apply (
      { pexp_desc = Pexp_ident { txt = printf_sprintf ; _};_},
      (
        Nolabel,
        { pexp_desc = Pexp_constant(
              Pconst_string("%s",_,_));_})::
      _)
    when OCAML_AST.longident_name printf_sprintf = "Printf.printf"
    ->
      let msg =
        {|'Printf.printf "%s"' should be replaced by 'print_string'|}
      in
      Some (w, Some msg, { config with w_useless_sprintf = None; })

  (* Note that we could also warn to use an iterator instead *)
  | { w_suspicious_for_zero_to_len = Some w ; _ },
    Pexp_for( _,
              { pexp_desc =
                  Pexp_constant (Pconst_integer ("0",_));_},
              { pexp_desc =
                  Pexp_apply (
                    { pexp_desc = Pexp_ident { txt = length;_};_},
                    [_]);_},
              _,
              _)
    when
      match OCAML_AST.longident_name length with
      | "Array.length" | "String.length" -> true
      | _ -> false
    ->
      Some (w, None, { config with w_suspicious_for_zero_to_len = None; })

  | { w_fun_fun = Some w ; _ }, _ when check_fun_fun e ->
      Some (w, None, { config with w_fun_fun = None; })

  | _ -> None

let register ns
    ~tags:common_tags
    config
  =
  let warnings = ref [] in
  let some x =
    warnings := x :: !warnings ;
    Some x
  in
  let warning_of_desc config desc =
    match config with
    | None -> None
    | Some id ->
        some @@
        YALO.new_warning_of_desc ns ~desc id ~tags:common_tags
  in
  let w_string_concat =
    warning_of_desc config.w_string_concat msg.w_string_concat
  in

  let w_incr_decr =
    warning_of_desc config.w_incr_decr msg.w_incr_decr
  in

  let w_comp_boolean =
    warning_of_desc config.w_comp_boolean msg.w_comp_boolean
  in

  let w_failwith_sprintf =
    warning_of_desc config.w_failwith_sprintf msg.w_failwith_sprintf
  in

  let w_list_length_comp_zero =
    warning_of_desc config.w_list_length_comp_zero msg.w_list_length_comp_zero
  in

  let w_list_length_comp_any =
    warning_of_desc config.w_list_length_comp_any msg.w_list_length_comp_any
  in

  let w_list_length_comp_list_length =
    warning_of_desc config.w_list_length_comp_list_length
      msg.w_list_length_comp_list_length
  in

  let w_then_bool_else_bool =
    warning_of_desc config.w_then_bool_else_bool msg.w_then_bool_else_bool
  in

  let w_then_or_else_bool =
    warning_of_desc config.w_then_or_else_bool msg.w_then_or_else_bool
  in

  let w_else_unit =
    warning_of_desc config.w_else_unit msg.w_else_unit
  in

  let w_try_catch_all =
    warning_of_desc config.w_try_catch_all msg.w_try_catch_all
  in

  let w_list_append_for_one =
    warning_of_desc config.w_list_append_for_one msg.w_list_append_for_one
  in

  let w_useless_sprintf =
    warning_of_desc config.w_useless_sprintf msg.w_useless_sprintf
  in

  let w_suspicious_for_zero_to_len =
    warning_of_desc config.w_suspicious_for_zero_to_len
      msg.w_suspicious_for_zero_to_len
  in

  let w_fun_fun =
    warning_of_desc config.w_fun_fun msg.w_fun_fun
  in

  let config = {
    w_string_concat ;
    w_incr_decr ;
    w_comp_boolean ;
    w_failwith_sprintf ;
    w_list_length_comp_zero ;
    w_list_length_comp_any ;
    w_list_length_comp_list_length ;
    w_then_bool_else_bool ;
    w_then_or_else_bool ;
    w_else_unit ;
    w_try_catch_all ;
    w_list_append_for_one ;
    w_useless_sprintf ;
    w_suspicious_for_zero_to_len ;
    w_fun_fun ;
  } in

  OCAML_LANG.new_ast_impl_traverse_linter ns
    "check:untyped_in_one_pass"
    ~warnings:!warnings
    (fun ~file:_ ~linter traverse ->


       let expression ~file ~linter e =
         let rec iter ~file ~linter config e =
           match find_warning config e with
           | None -> ()
           | Some (w, msg, config) ->
               YALO.warn ~loc:e.pexp_loc ~file ?msg ~linter w;
               iter ~file ~linter config e
         in
         iter ~file ~linter config e
       in
       traverse.expression <- (linter, expression) :: traverse.expression
    );
  ()
