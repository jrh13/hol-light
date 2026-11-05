#!/bin/bash

# Makefile will replace __DIR__ with the path
export HOLLIGHT_DIR=__DIR__
export HOLLIGHT_USE_MODULE=__USE_MODULE__

if [ "$#" -eq 1 ]; then
  if [ "$1" == "-pp" ]; then
    echo "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"${HOLLIGHT_DIR}\" pa_j.cmo"
    exit 0
  elif [ "$1" == "-dir" ]; then
    echo "${HOLLIGHT_DIR}"
    exit 0
  elif [ "$1" == "-use-module" ]; then
    echo "${HOLLIGHT_USE_MODULE}"
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
  -use-module     print 1 if HOL Light was built as a module (hol_lib), else 0
  -version        print the HOL Light version and commit hash
  -help           print this message

Commands available when built with HOLLIGHT_USE_MODULE=1:
  inline-load <input.ml> <output.ml>
                  inline the loads/loadt/needs calls of <input.ml>
  compile <input.ml> [ocamlopt options]
                  compile <input.ml> natively against hol_lib (<input.cmx>)
  link <input.cmx> -o <output> [ocamlopt options]
                  link a native executable with hol_lib
  compile-byte <input.ml> [ocamlc options]
                  compile <input.ml> to bytecode against hol_lib (<input.cmo>)
  link-byte <input.cmo> -o <output> [ocamlc options]
                  link a bytecode executable with hol_lib

Environment variables:
  LINE_EDITOR     line editor wrapping the toplevel (default: ledit)
  HOL_ML_PATH     file loaded at startup instead of \${HOLLIGHT_DIR}/hol.ml
EOF
    exit 0
  fi
fi

# If a local OPAM is installed, use it
if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  eval $(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)
fi

if [ "$#" -gt 1 ]; then
  if [ "$1" == "inline-load" ]; then
    # Do the inlining.
    shift
    ocaml "${HOLLIGHT_DIR}/inline_load.ml" "$@"
    exit $?

  elif [ "$1" == "compile" ]; then
    # Native-compile the source code using ocamlopt.
    shift
    OCAMLRUNPARAM=l=2000000000 ocamlopt.byte \
        -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"${HOLLIGHT_DIR}\" pa_j.cmo" \
        -I "${HOLLIGHT_DIR}" -I +unix -c \
        hol_lib.cmxa "$@"
    exit $?

  elif [ "$1" == "link" ]; then
    # Link the native module
    shift
    ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
        -I "${HOLLIGHT_DIR}" "$@"
    exit $?

  elif [ "$1" == "compile-byte" ]; then
    # Compile the source code to OCaml bytecode using ocamlc.
    shift
    ocamlfind ocamlc -package zarith,unix \
        -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"${HOLLIGHT_DIR}\" pa_j.cmo" \
        -I "${HOLLIGHT_DIR}" -c "$@"
    exit $?

  elif [ "$1" == "link-byte" ]; then
    # Link the bytecode module
    shift
    ocamlfind ocamlc -package zarith,unix -linkpkg hol_lib.cma \
        -I "${HOLLIGHT_DIR}" "$@"
    exit $?

  fi
fi

# The default ocaml REPL does not accept arrow keys.
# Export LINE_EDITOR to a proper program to enable this before invoking this
# script. If not set, ledit will be used.
if [ "${LINE_EDITOR}" == "" ]; then
  LINE_EDITOR="ledit"
fi

# If a custom hol.ml is given, use it. This variable is used by make-checkpoint.sh .
if [ "${HOL_ML_PATH}" == "" ]; then
  HOL_ML_PATH="${HOLLIGHT_DIR}/hol.ml"
fi

${LINE_EDITOR} ${HOLLIGHT_DIR}/ocaml-hol -init ${HOL_ML_PATH} -I ${HOLLIGHT_DIR}
