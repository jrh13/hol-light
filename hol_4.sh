#!/bin/bash

# Makefile will replace __DIR__ with the path
export HOLLIGHT_DIR=__DIR__

if [ "$#" -eq 1 ]; then
  if [ "$1" == "-pp" ]; then
    echo "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I "__DIR__" pa_j.cmo"
    exit 0
  elif [ "$1" == "-dir" ]; then
    echo "${HOLLIGHT_DIR}"
    exit 0
  elif [ "$1" == "-version" ]; then
    # The version is the one in the opam file. The commit is taken from git if
    # HOLLIGHT_DIR is a git checkout, and otherwise is the one recorded when
    # this script was generated.
    COMMIT=""
    if [ -e "${HOLLIGHT_DIR}/.git" ]; then
      COMMIT=`git -C "${HOLLIGHT_DIR}" rev-parse HEAD 2>/dev/null`
    fi
    if [ "${COMMIT}" == "" ]; then
      COMMIT="__COMMIT__"
    else
      COMMIT="commit ${COMMIT}"
    fi
    echo "HOL Light version __VERSION__ (${COMMIT})"
    exit 0
  elif [ "$1" == "-help" ] || [ "$1" == "--help" ]; then
    cat <<EOF
Usage: hol.sh [command]

Without a command, start the OCaml toplevel with HOL Light loaded.

Commands:
  -pp             print the camlp5 preprocessor command for HOL Light syntax
  -dir            print the HOL Light directory
  -version        print the HOL Light version and commit hash
  -help           print this message

Environment variables:
  LINE_EDITOR     line editor wrapping the toplevel (default: ledit)
  HOL_ML_PATH     file loaded at startup instead of \${HOLLIGHT_DIR}/hol.ml
EOF
    exit 0
  fi
fi

# The default ocaml REPL does not accept arrow keys.
# Export LINE_EDITOR to a proper program to enable this before invoking this
# script. If not set, ledit will be used.
if [ "${LINE_EDITOR}" == "" ]; then
  LINE_EDITOR="ledit"
fi

export HOLLIGHT_USE_MODULE=__USE_MODULE__

# If a local OPAM is installed, use it
if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  eval $(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)
fi

# If a custom hol.ml is given, use it. This variable is used by make-checkpoint.sh .
if [ "${HOL_ML_PATH}" == "" ]; then
  HOL_ML_PATH="${HOLLIGHT_DIR}/hol.ml"
fi

${LINE_EDITOR} ${HOLLIGHT_DIR}/ocaml-hol -I `camlp5 -where` camlp5o.cma -init ${HOL_ML_PATH} -safe-string -I ${HOLLIGHT_DIR}
