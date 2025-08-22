OCAMLC = ocamlc
OCAMLFIND = ocamlfind
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLCPARAM = -g

TYPES_SOURCES = ocamlTypes.ml types_parser.ml types_lexer.ml
TYPES_OBJECTS = $(TYPES_SOURCES:.ml=.cmo)

all: types_test tracer

tracer: $(TYPES_OBJECTS) tracer.ml
	$(OCAMLFIND) $(OCAMLC) -package compiler-libs.common $(OCAMLCPARAM) -linkpkg -o tracer $^

types_test: $(TYPES_OBJECTS) types_test.ml
	$(OCAMLC) $(OCAMLCPARAM) -o $@ $^

types_parser.ml types_parser.mli: types_parser.mly
	$(OCAMLYACC) types_parser.mly

types_lexer.ml: types_lexer.mll
	$(OCAMLLEX) types_lexer.mll

%.cmo: %.ml
	$(OCAMLFIND) $(OCAMLC) -package compiler-libs.common $(OCAMLCPARAM) -c $<

%.cmi: %.mli
	$(OCAMLFIND) $(OCAMLC) -package compiler-libs.common $(OCAMLCPARAM) -c $<

# Dependencies
types_test.cmo: ocamlTypes.cmo types_parser.cmo types_lexer.cmo
types_parser.cmo: types_parser.ml types_parser.cmi ocamlTypes.cmo ocamlTypes.cmi
types_lexer.cmo: types_lexer.ml types_parser.cmo
ocamlTypes.cmo: ocamlTypes.ml

clean:
	rm -f *.cmo *.cmi tracer types_test types_parser.ml types_parser.mli types_lexer.ml

.PHONY: all clean
