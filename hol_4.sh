#!/bin/bash

# The default ocaml REPL does not accept arrow keys.
# Export LINE_EDITOR to a proper program to enable this before invoking this
# script. If not set, ledit will be used.
if [ "${LINE_EDITOR}" == "" ]; then
  LINE_EDITOR="ledit"
fi

# Makefile will replace __DIR__ with the path
export HOLLIGHT_DIR=__DIR__
export HOLLIGHT_USE_MODULE=__USE_MODULE__

# If a local OPAM is installed, use it
if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  eval $(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)
fi

${LINE_EDITOR} ${HOLLIGHT_DIR}/ocaml-hol -I `camlp5 -where` camlp5o.cma -init ${HOLLIGHT_DIR}/hol.ml -safe-string -I ${HOLLIGHT_DIR}
