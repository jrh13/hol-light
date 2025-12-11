OCAMLC = ocamlc
OCAMLFIND = ocamlfind
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLCPARAM = -g

TYPES_SOURCES = ocamlTypes.ml types_parser.ml types_lexer.ml
TYPES_OBJECTS = $(TYPES_SOURCES:.ml=.cmo)

# Set the HOLLIGHT_DIR to <this Makefile>/..
HOLLIGHT_DIR?=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))/..

TESTS =\
  examples/tactic.ml \
  examples/conv.ml

TEST_OUTPUTS = $(TESTS:.ml=.outdir)


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

test: $(TEST_OUTPUTS)

examples/%.outdir: examples/%.ml tracer
	if [ `$(HOLLIGHT_DIR)/hol.sh -use-module` -eq 0 ]; then echo "HOLLIGHT_USE_MODULE unset"; exit 0; fi
	$(HOLLIGHT_DIR)/hol.sh inline-load $< $(basename $<)_inlined.ml
	HOLLIGHT_DIR=$(HOLLIGHT_DIR) $(HOLLIGHT_DIR)/TacticTrace/modify-proof.sh $(basename $<)_inlined.ml $(basename $<)_inlined_wrapped.ml $(basename $<).outdir
	$(HOLLIGHT_DIR)/hol.sh compile $(basename $<)_inlined_wrapped.ml -o $(basename $<).cmx
	$(HOLLIGHT_DIR)/hol.sh link $(basename $<).cmx -o $(basename $<).native
	$(basename $<).native > $(basename $<).hollog # Use cat to strip ANSI color codes


clean:
	rm -f *.cmo *.cmi tracer types_test types_parser.ml types_parser.mli types_lexer.ml kernel_wrapper.ml
	rm -rf $(TEST_OUTPUTS) examples/*.cm* examples/*_inlined* examples/*.o examples/*.hollog examples/*.native

.PHONY: all clean
