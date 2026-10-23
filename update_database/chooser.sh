#!/bin/bash

OCAML_VERSION=`ocamlc -version | cut -c1-4`
OCAML_BINARY_VERSION=`ocamlc -version | cut -c1-3`
OCAML_UNARY_VERSION=`ocamlc -version | cut -c1`

# update_database_5.4.ml covers OCaml 5.4 and later; the compiler-libs
# interfaces it relies on (Env.fold_values/fold_modules, Longident and
# Toploop) are unchanged in 5.5.

if [ ${OCAML_BINARY_VERSION} = "5.4" -o ${OCAML_BINARY_VERSION} = "5.5" ]
then
  echo "update_database_5.4.ml"
elif [ ${OCAML_VERSION} = "4.14" ]
then
  echo "update_database_4.14.ml"
else
  echo "update_database_${OCAML_UNARY_VERSION}.ml"
fi
