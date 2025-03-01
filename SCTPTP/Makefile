
.PHONY = default 

default: all

all: 
	ocamllex tptplexer.mll
	ocamlc tptphelpers.ml tptpast.ml
	menhir --infer tptpparser.mly
	ocamlc tptphelpers.ml tptpast.ml tptpparser.mli tptpparser.ml tptplexer.ml tptplink.ml

clean:
	rm -f *.cmi *.cmo tptpparser.ml tptpparser.mli tptplexer.ml