if [ ! -d "$HOLLIGHT_DIR" ]; then
  echo "HOLLIGHT_DIR is not set: $HOLLIGHT_DIR"
  echo "Please do 'export HOLLIGHT_DIR=<the path to your hol-light>"
  exit 1
elif [ ! -d "$TACLOGGER_DIR" ]; then
  echo "TACLOGGER_DIR is not set: $TACLOGGER_DIR"
  echo "Please do 'export TACLOGGER_DIR=<the path to your HOLLightTacLogger>"
  exit 1
fi

eval $(opam env --switch $HOLLIGHT_DIR --set-switch)
ocaml --version

make clean
make

# The AST!
# Also get types of definitions
cp $HOLLIGHT_DIR/hol_lib_inlined.ml hol_lib_inlined.org.ml

# Remove the line number directives first.
python3 ${TACLOGGER_DIR}/remove-linenum-dirs.py hol_lib_inlined.org.ml hol_lib_inlined.ml

./get-ast.sh hol_lib_inlined.ml

# Get locations of tactic definitions
./tracer make-wrappers hol_lib_inlined.org.ml hol_lib_inlined.marshalled.bin hol_lib_inlined.mli kernel_wrapper.ml
