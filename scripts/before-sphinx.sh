#!/bin/sh

INCLUDES="-I ./_build/install/default/lib/yalo_plugin_ocaml -I ./_build/install/default/lib/yalo_plugin_YALO -I ./_build/install/default/lib/yalo_plugin_FIND -I ./_build/install/default/lib/yalo_lib -I ./_build/install/default/lib/yalo_plugin_ZANUDA -I ./_build/install/default/lib/yalo_plugin_CAMELOT -I ./_build/install/default/lib/yalo_plugin_OCPINDENT -I share"

./_build/default/src/yalo/main.exe ${INCLUDES} commands-rst > sphinx/commands.rst
./_build/default/src/yalo/main.exe options-rst > sphinx/options.rst
