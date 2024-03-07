#!/bin/bash

# The default ocaml REPL does not accept arrow keys.
# Export LINE_EDITOR to a proper program to enable this before invoking this
# script. ledit and rlwrap are good candidates.

# Makefile will replace __DIR__ with the path
export HOLLIGHT_DIR=__DIR__
${LINE_EDITOR} ${HOLLIGHT_DIR}/ocaml-hol -init ${HOLLIGHT_DIR}/hol.ml -safe-string
