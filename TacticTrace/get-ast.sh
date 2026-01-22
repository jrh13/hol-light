if [ "$#" -ne 1 ]; then
  echo "get-ast.sh <input.ml>"
  exit 1
fi

if [ ! -d "$HOLLIGHT_DIR" ]; then
  echo "HOLLIGHT_DIR is not set: $HOLLIGHT_DIR"
  echo "Please do 'export HOLLIGHT_DIR=<the path to your hol-light>'"
  exit 1
fi

eval $(opam env --switch $HOLLIGHT_DIR --set-switch)

# The AST!
inp=$1

outp=${inp%.ml}.marshalled.bin
camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I $HOLLIGHT_DIR pa_j.cmo \
    $inp > $outp

outip=${inp%.ml}.mli
ocamlc -pp "`$HOLLIGHT_DIR/hol.sh -pp`" -I "$HOLLIGHT_DIR" -i $inp > $outip
