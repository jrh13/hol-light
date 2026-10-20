# The Four Colour Theorem in HOL Light -- see make.ml for the structure.
# All paths in the sources are "4CT/<file>", so everything runs from the
# PARENT directory (which is on HOL Light's default load path "." when HOL
# is started there); Autoformalization/planar_graph.ml and eval_compile/ must
# be found there too or under the HOL Light root ("$" on the load path).
#
#   make native        build the native binary: with OCaml 5 or later the
#                      parallel one (make_parallel.ml), otherwise the
#                      sequential one (make.ml); see PARALLEL below.  The
#                      compile takes ~2.5 h and ~50 GB, since Multivariate
#                      is inlined
#   make run-native    run it: Multivariate, the whole development and the
#                      633 checks; prints FOUR_COLOR, FOUR_COLOR_PLANAR_GRAPH,
#                      FOUR_COLOR_MAP and the other forms (sequential
#                      ~11 h, ~1 GB; parallel ~22 min, ~48 GB on 128 cores)
#   make run-bytecode  the same in the HOL Light bytecode toplevel
#                      (sequential ~2 days; parallel ~1.5 h, ~60 GB)
#   make native-hypermap, make run-native-hypermap, make run-bytecode-hypermap
#                      the same for the hypermap theorem FOUR_COLOR alone
#                      (Parts 1 and 2, no Multivariate): the native compile
#                      takes ~7 min and ~7 GB, the run ~10.5 h sequential
#                      or ~15 min parallel
#   make compiled      regenerate part2_compiled.hl (bytecode; loads the
#                      development first; reflow79.py then re-wraps the
#                      generated code to 79 columns, whitespace only)
#   make clean         remove the native build products (native_build/
#                      keeps dedupe_inlined.py)
#   make clobber       make clean, and remove the generated evaluator
#                      part2_compiled.hl too (the native builds then
#                      regenerate it first, as make compiled does: ~15 min
#                      in bytecode).  presentations_data.ml and
#                      configurations.ml are also generated, from the Coq
#                      sources, but not by this package, so they stay
#
# PARALLEL=yes runs the presentation side conditions and the 633 checks in
# FOURCOLOR_DOMAINS OCaml domains of one process (parallel.ml, OCaml 5 or
# later; default the number of cores, at most 128); PARALLEL=no runs
# everything sequentially, as with OCaml 4.  The default is yes exactly when
# ocamlopt is version 5 or later.  The *-sequential and *-parallel targets
# force either variant.
#
# Native compilation: hol.sh inline-load textually inlines every needs/loadt
# (dedupe_inlined.py keeps the first copy of each file, as `needs` would), the
# Str (and, for the parallel variant, Unix) #load directives are dropped and
# the libraries linked instead.  `ulimit -s unlimited` for the deep-recursion
# proofs.

PARENT := $(abspath $(CURDIR)/..)
# the hol.sh of the HOL Light tree containing 4CT, else ~/hol-light's
HOL    ?= $(firstword $(wildcard $(PARENT)/hol.sh) $(HOME)/hol-light/hol.sh)
NB     := native_build

OCAML_MAJOR := $(shell ocamlfind ocamlopt -version 2>/dev/null | cut -d. -f1)
PARALLEL ?= $(shell test "0$(OCAML_MAJOR)" -ge 5 && echo yes || echo no)

ifeq ($(PARALLEL),yes)
VARIANT := parallel
else
VARIANT := sequential
endif

# every source file, so that any edit rebuilds the binaries
SRCS := $(wildcard *.ml *.hl ../eval_compile/*.hl)

.PHONY: native run-native run-bytecode compiled \
        native-sequential run-native-sequential run-bytecode-sequential \
        native-parallel run-native-parallel run-bytecode-parallel

native: native-$(VARIANT)
run-native: run-native-$(VARIANT)
run-bytecode: run-bytecode-$(VARIANT)

# $(call native_rule,DRIVER,BINARY): inline DRIVER (a 4CT/... path) and
# compile it to $(NB)/BINARY
define native_rule
	cd $(PARENT) && bash $(HOL) inline-load $(1) 4CT/$(NB)/$(2)_inlined.ml
	cd $(NB) && python3 dedupe_inlined.py $(2)_inlined.ml $(2).ml
	cd $(NB) && sed -i -e 's/^#load "str.cma";;//' \
	  -e 's/^#load "unix.cma";;//' -e 's/^#directory "+unix";;//' $(2).ml
	cd $(NB) && bash $(HOL) compile -I +str $(2).ml
	cd $(NB) && bash $(HOL) link -package str $(2).cmx -o $(2)
endef

# ---- make.ml, sequential and parallel

native-sequential: $(NB)/fourcolor_native

$(NB)/fourcolor_native: $(SRCS) | part2_compiled.hl
	$(call native_rule,4CT/make.ml,fourcolor_native)

run-native-sequential: $(NB)/fourcolor_native
	cd $(NB) && ulimit -s unlimited && ./fourcolor_native

run-bytecode-sequential:
	cd $(PARENT) && ulimit -s unlimited && \
	  echo 'loadt "4CT/make.ml";;' | bash $(HOL)

native-parallel: $(NB)/fourcolor_par_native

$(NB)/fourcolor_par_native: $(SRCS) | part2_compiled.hl
	$(call native_rule,4CT/make_parallel.ml,fourcolor_par_native)

run-native-parallel: $(NB)/fourcolor_par_native
	cd $(NB) && ulimit -s unlimited && ./fourcolor_par_native

run-bytecode-parallel:
	cd $(PARENT) && ulimit -s unlimited && \
	  echo 'loadt "4CT/make_parallel.ml";;' | bash $(HOL)

compiled:
	cd $(PARENT) && ulimit -s unlimited && \
	  echo 'loadt "4CT/part2_compile.ml";;' | bash $(HOL)
	python3 reflow79.py --apply part2_compiled.hl

# only when it is missing (make clobber): the binaries have it as an
# order-only prerequisite, so a newer part2_eval.ml does not trigger this
part2_compiled.hl:
	$(MAKE) compiled

# ---- the hypermap theorem alone: part2_final.ml proves FOUR_COLOR from
# ---- Parts 1 and 2 without Multivariate; the drivers are generated

HYP_SEQ := $(NB)/make_hypermap.ml
HYP_PAR := $(NB)/make_hypermap_parallel.ml
HYP_RUN := 'needs "4CT/part2_final.ml";;' \
           'let REDUCIBILITY, FOUR_COLOR = p2_final();;'

.PHONY: native-hypermap run-native-hypermap run-bytecode-hypermap \
        native-hypermap-sequential run-native-hypermap-sequential \
        native-hypermap-parallel run-native-hypermap-parallel

native-hypermap: native-hypermap-$(VARIANT)
run-native-hypermap: run-native-hypermap-$(VARIANT)

$(HYP_SEQ):
	printf '(* FOUR_COLOR alone (generated by the Makefile) *)\n' > $@
	printf '%s\n' $(HYP_RUN) >> $@

$(HYP_PAR):
	printf '(* FOUR_COLOR alone (generated by the Makefile) *)\n' > $@
	printf '%s\n' 'needs "4CT/parallel.ml";;' $(HYP_RUN) >> $@

native-hypermap-sequential: $(NB)/fourcolor_hypermap_native

$(NB)/fourcolor_hypermap_native: $(HYP_SEQ) $(SRCS) | part2_compiled.hl
	$(call native_rule,4CT/$(HYP_SEQ),fourcolor_hypermap_native)

run-native-hypermap-sequential: $(NB)/fourcolor_hypermap_native
	cd $(NB) && ulimit -s unlimited && ./fourcolor_hypermap_native

native-hypermap-parallel: $(NB)/fourcolor_hypermap_par_native

$(NB)/fourcolor_hypermap_par_native: $(HYP_PAR) $(SRCS) | part2_compiled.hl
	$(call native_rule,4CT/$(HYP_PAR),fourcolor_hypermap_par_native)

run-native-hypermap-parallel: $(NB)/fourcolor_hypermap_par_native
	cd $(NB) && ulimit -s unlimited && ./fourcolor_hypermap_par_native

run-bytecode-hypermap: $(HYP_SEQ) $(HYP_PAR)
ifeq ($(PARALLEL),yes)
	cd $(PARENT) && ulimit -s unlimited && \
	  echo 'loadt "4CT/$(HYP_PAR)";;' | bash $(HOL)
else
	cd $(PARENT) && ulimit -s unlimited && \
	  echo 'loadt "4CT/$(HYP_SEQ)";;' | bash $(HOL)
endif

.PHONY: clean clobber
clean:
	rm -f $(NB)/*_inlined.ml $(NB)/*_native.ml $(NB)/*.cmi $(NB)/*.cmx \
	  $(NB)/*.o $(NB)/fourcolor_native $(NB)/fourcolor_par_native \
	  $(NB)/fourcolor_hypermap_native $(NB)/fourcolor_hypermap_par_native \
	  $(HYP_SEQ) $(HYP_PAR)

clobber: clean
	rm -f part2_compiled.hl
