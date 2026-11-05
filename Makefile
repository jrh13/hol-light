###############################################################################
# Makefile for HOL Light                                                      #
#                                                                             #
# Simple "make" just builds the camlp4/camlp5 syntax extension "pa_j.cmo",    #
# which is necessary to load the HOL Light core into the OCaml toplevel.      #
#                                                                             #
# See the README file for more detailed information about the build process.  #
#                                                                             #
# Thanks to Carl Witty for 3.07 and 3.08 ports of pa_j.ml and this process.   #
###############################################################################

# Installation directory for standalone binaries. Set here to the user's
# binary directory. You may want to change it to something like /usr/local/bin

BINDIR=${HOME}/bin

# This is the list of source files in the HOL Light core

HOLSRC=system.ml lib.ml fusion.ml basics.ml nets.ml preterm.ml          \
       parser.ml printer.ml equal.ml bool.ml drule.ml tactics.ml        \
       itab.ml simp.ml theorems.ml ind_defs.ml class.ml trivia.ml       \
       canon.ml meson.ml firstorder.ml metis.ml thecops.ml quot.ml      \
       impconv.ml recursion.ml pair.ml compute.ml                       \
       nums.ml arith.ml wf.ml calc_num.ml normalizer.ml grobner.ml      \
       ind_types.ml lists.ml realax.ml calc_int.ml realarith.ml         \
       real.ml calc_rat.ml int.ml sets.ml iterate.ml cart.ml define.ml  \
       help.ml database.ml update_database.ml hol_lib.ml hol_loader.ml

# Some parameters to help decide how to build things

OCAML_VERSION=`ocamlc -version | cut -c1-4`
OCAML_BINARY_VERSION=`ocamlc -version | cut -c1-3`
OCAML_UNARY_VERSION=`ocamlc -version | cut -c1`

# If set to 1, build hol_lib.cmo and make hol.sh to use it.
# NOTE: This extends the trusted base of HOL Light to include the inliner
# script, inline_load.ml. inline_load.ml is an OCaml program that receives
# an HOL Light proof and replaces the loads/loadt/needs function invocations
# with their actual contents. Please turn this flag on only if having this
# additional trusted base is considered okay.
#
# The setting is remembered in 'config.mk', so it only has to be given once:
# 'make HOLLIGHT_USE_MODULE=1' (or 'HOLLIGHT_USE_MODULE=1 make') records it,
# and later plain 'make' invocations reuse it until a different value is given
# explicitly. 'make distclean' forgets it.
#
# config.mk is only read here (it is not included as a makefile), and it is
# only written by the recipe of the 'config.mk' target below, so previewing or
# querying a build ('make -n', 'make -q') never changes the saved setting.

CONFIG_FILE=config.mk

ifeq ($(origin HOLLIGHT_USE_MODULE),undefined)
HOLLIGHT_USE_MODULE:=$(shell sed -n 's/^HOLLIGHT_USE_MODULE=//p' $(CONFIG_FILE) 2>/dev/null)
ifeq ($(HOLLIGHT_USE_MODULE),)
HOLLIGHT_USE_MODULE:=0
endif
endif

# The version (from the opam file) and the git commit printed by 'hol.sh -version'

HOLLIGHT_VERSION:=$(shell sed -n 's/^version: *"\(.*\)"/\1/p' opam)
HOLLIGHT_COMMIT:=$(shell h=`test -e .git && git rev-parse HEAD 2>/dev/null` && echo "commit $$h" || echo "commit unknown")

# Main target

default: update_database.ml pa_j.cmo hol.sh;

# Save the configuration, writing config.mk only if the value has changed.

$(CONFIG_FILE): FORCE
	@echo "HOLLIGHT_USE_MODULE=$(HOLLIGHT_USE_MODULE)" | cmp -s - $(CONFIG_FILE) || \
	  echo "HOLLIGHT_USE_MODULE=$(HOLLIGHT_USE_MODULE)" > $(CONFIG_FILE)

FORCE:

# Create a local OPAM switch and install dependencies on it.
# This will use the latest OCaml version that fully supports features of
# HOL Light.
# Use --no-install to avoid installing HOL Light itself through the opam file
# in this directory; the dependencies are then installed with --deps-only,
# so that the versions actually used (camlp5, zarith and ledit, the last for
# line editing of the OCaml REPL) are the ones that the opam file asks for
# rather than a second, hand-maintained list that can drift away from it.
# The camlp5 that OPAM chose is then pinned to that same version: the opam file
# binds only while the dependencies are resolved, and HOL Light itself is not
# installed here, so an 'opam upgrade' could otherwise move camlp5 out of range.
switch:; \
  opam update ; \
  opam switch create . ocaml-base-compiler.4.14.0 --no-install ; \
  eval $$(opam env) ; \
  opam install -y . --deps-only && \
  opam pin add -y -n camlp5 $$(opam var camlp5:version)

switch-5:; \
  opam update ; \
  opam switch create . ocaml-base-compiler.5.5.2 --no-install ; \
  eval $$(opam env) ; \
  opam install -y . --deps-only && \
  opam pin add -y -n camlp5 $$(opam var camlp5:version)

# Choose an appropriate "update_database.ml" file

update_database.ml:; \
  cp update_database/`update_database/chooser.sh` update_database.ml

# Build the camlp4 syntax extension file (camlp5 for OCaml >= 3.10)

pa_j.cmo: pa_j.ml; if test ${OCAML_BINARY_VERSION} = "3.0" ; \
                   then ocamlc -c -pp "camlp4r pa_extend.cmo q_MLast.cmo" -I `camlp4 -where` pa_j.ml ; \
                   elif test ${OCAML_BINARY_VERSION} = "3.1" -o ${OCAML_VERSION} = "4.00" -o ${OCAML_VERSION} = "4.01"  -o ${OCAML_VERSION} = "4.02" -o ${OCAML_VERSION} = "4.03" -o ${OCAML_VERSION} = "4.04" -o ${OCAML_VERSION} = "4.05" ; \
                   then ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` pa_j.ml ; \
                   else ocamlc -safe-string -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` -I `ocamlfind query camlp-streams` pa_j.ml ; \
                   fi

pa_j.ml: pa_j/pa_j_3.07.ml pa_j/pa_j_3.08.ml pa_j/pa_j_3.09.ml \
         pa_j/pa_j_3.1x_5.xx.ml pa_j/pa_j_3.1x_6.xx.ml \
         pa_j/pa_j_4.xx_8.00.ml pa_j/pa_j_4.xx_8.02.ml \
         pa_j/pa_j_4.xx_8.03.ml pa_j/pa_j_4.xx_8.03.06.ml \
         pa_j/pa_j_8.04.00.ml ; \
  cp pa_j/`pa_j/chooser.sh` pa_j.ml

# Choose an appropriate bignum library.

bignum.cmo: bignum_zarith.ml bignum_num.ml ; \
        if test ${OCAML_VERSION} = "4.14" -o ${OCAML_UNARY_VERSION} = "5" ; \
        then ocamlfind ocamlc -package zarith -c -o bignum.cmo bignum_zarith.ml ; \
        else ocamlc -c -o bignum.cmo bignum_num.ml ; \
        fi

bignum.cmx: bignum_zarith.ml bignum_num.ml ; \
        if test ${OCAML_VERSION} = "4.14" -o ${OCAML_UNARY_VERSION} = "5" ; \
        then ocamlfind ocamlopt -package zarith -c -o bignum.cmx bignum_zarith.ml ; \
        else ocamlopt -c -o bignum.cmx bignum_num.ml ; \
        fi

hol_loader.cmo: hol_loader.ml ; \
        ocamlc -verbose -c hol_loader.ml -o hol_loader.cmo

hol_loader.cmx: hol_loader.ml ; \
        ocamlopt -verbose -c hol_loader.ml -o hol_loader.cmx

hol_lib_inlined.ml: ${HOLSRC} inline_load.ml ; \
        HOLLIGHT_DIR="`pwd`" ocaml inline_load.ml hol_lib.ml hol_lib_inlined.ml -omit-prelude

hol_lib.cmo: pa_j.cmo hol_lib_inlined.ml hol_loader.cmo bignum.cmo ; \
        ocamlc -verbose -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I . pa_j.cmo" hol_loader.cmo hol_lib_inlined.ml bignum.cmo -o hol_lib.cmo

hol_lib.cma: hol_lib.cmo bignum.cmo hol_loader.cmo ; \
        ocamlfind ocamlc -package zarith -linkpkg -a -o hol_lib.cma bignum.cmo hol_loader.cmo hol_lib.cmo

hol_lib.cmx: pa_j.cmo hol_lib_inlined.ml hol_loader.cmx bignum.cmx ; \
        OCAMLRUNPARAM=l=1000000000 ocamlopt.byte -verbose -c \
              -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I . pa_j.cmo" \
              hol_lib_inlined.ml hol_loader.cmx bignum.cmx -o hol_lib.cmx

hol_lib.cmxa: hol_lib.cmx hol_loader.cmx bignum.cmx ; \
        ocamlfind ocamlopt -package zarith -a -o hol_lib.cmxa bignum.cmx hol_loader.cmx hol_lib.cmx

# Create a bash script 'hol.sh' that loads 'hol.ml' in OCaml REPL.
#
# hol.sh records the HOLLIGHT_USE_MODULE setting it was generated with. It is
# regenerated whenever that differs from the current setting. This compares
# the values themselves rather than timestamps, which may be too coarse to
# order config.mk and hol.sh when the setting is changed quickly.

HOLSH_USE_MODULE:=$(shell sed -n 's/^export HOLLIGHT_USE_MODULE=//p' hol.sh 2>/dev/null)
ifneq ($(HOLSH_USE_MODULE),$(HOLLIGHT_USE_MODULE))
hol.sh: FORCE
endif

hol.sh: pa_j.cmo ${HOLSRC} bignum.cmo hol_loader.cmo update_database.ml \
        hol_4.sh hol_4.14.sh $(wildcard opam) | $(CONFIG_FILE)
	if [ `uname` = "Linux" ] || [ `uname` = "Darwin" ] ; then \
		if [ ${OCAML_UNARY_VERSION} = "5" ] || [ ${OCAML_VERSION} = "4.14" ] ; then \
			ocamlfind ocamlmktop -package zarith -o ocaml-hol zarith.cma bignum.cmo hol_loader.cmo ; \
			sed "s^__DIR__^`pwd`^g; s^__USE_MODULE__^$(HOLLIGHT_USE_MODULE)^g; s^__VERSION__^$(HOLLIGHT_VERSION)^g; s^__COMMIT__^$(HOLLIGHT_COMMIT)^g" hol_4.14.sh > hol.sh ; \
		else \
			ocamlmktop -o ocaml-hol nums.cma bignum.cmo hol_loader.cmo ; \
			sed "s^__DIR__^`pwd`^g; s^__USE_MODULE__^$(HOLLIGHT_USE_MODULE)^g; s^__VERSION__^$(HOLLIGHT_VERSION)^g; s^__COMMIT__^$(HOLLIGHT_COMMIT)^g" hol_4.sh > hol.sh ; \
		fi ; \
		chmod +x hol.sh ; \
	else \
		echo 'FAILURE: hol.sh assumes Linux' ; \
	fi

# If HOLLIGHT_USE_MODULE is set, add hol_lib.cmo to dependency of hol.sh
# Also, build every test suite UnitTests/<name>.ml using both the OCaml
# bytecode compiler (UnitTests/<name>.byte) and the OCaml native compiler
# (UnitTests/<name>.native), through 'hol.sh compile/link' and
# 'hol.sh compile-byte/link-byte' respectively.

UNIT_TESTS=$(patsubst %.ml,%,$(filter-out %_inlined.ml,$(wildcard UnitTests/*.ml)))

ifeq ($(HOLLIGHT_USE_MODULE),1)
hol.sh: hol_lib.cmo

UnitTests/%_inlined.ml: UnitTests/%.ml inline_load.ml hol.sh ; \
        ./hol.sh inline-load $< $@
UnitTests/%_inlined.cmx: UnitTests/%_inlined.ml hol_lib.cmxa hol.sh ; \
        ./hol.sh compile $<
# Both compilers write UnitTests/<name>_inlined.cmi; serialize them so that
# a parallel make does not run the two at the same time.
UnitTests/%_inlined.cmo: UnitTests/%_inlined.ml hol_lib.cma hol.sh | UnitTests/%_inlined.cmx ; \
        ./hol.sh compile-byte $<
UnitTests/%.native: UnitTests/%_inlined.cmx hol_lib.cmxa hol.sh ; \
        ./hol.sh link $< -o $@
UnitTests/%.byte: UnitTests/%_inlined.cmo hol_lib.cma hol.sh ; \
        ./hol.sh link-byte $< -o $@

# Keep the intermediate files of the rules above.
.SECONDARY: $(addsuffix _inlined.ml,$(UNIT_TESTS)) \
            $(addsuffix _inlined.cmx,$(UNIT_TESTS)) \
            $(addsuffix _inlined.cmo,$(UNIT_TESTS))

default: hol_lib.cma hol_lib.cmxa \
         $(addsuffix .byte,$(UNIT_TESTS)) $(addsuffix .native,$(UNIT_TESTS))
endif

# Build a standalone hol image called "hol" (needs Linux and DMTCP)

hol: hol.sh make-checkpoint.sh update_database.ml;                      \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol "loadt \"update_database.ml\"" ;          \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with multivariate calculus preloaded.

hol.multivariate: hol.sh make-checkpoint.sh Multivariate/make.ml        \
     Library/card.ml Library/permutations.ml Library/products.ml        \
     Library/floor.ml Multivariate/misc.ml Library/iter.ml              \
     Multivariate/metric.ml Multivariate/vectors.ml                     \
     Multivariate/determinants.ml Multivariate/topology.ml              \
     Multivariate/convex.ml Multivariate/paths.ml                       \
     Multivariate/polytope.ml Multivariate/degree.ml                    \
     Multivariate/derivatives.ml Multivariate/clifford.ml               \
     Multivariate/integration.ml Multivariate/measure.ml                \
     Multivariate/multivariate_database.ml update_database.ml;          \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.multivariate "loadt \"Multivariate/make.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with analysis and SOS procedure preloaded

hol.sosa: hol.sh make-checkpoint.sh                                     \
     Library/analysis.ml Library/transc.ml                              \
     Examples/sos.ml update_database.ml;                                \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.sosa "loadt \"Library/analysis.ml\"; loadt \"Library/transc.ml\"; loadt \"Examples/sos.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with cardinal arithmetic preloaded

hol.card: hol.sh make-checkpoint.sh Library/card.ml update_database.ml; \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.card "loadt \"Library/card.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with multivariate-based complex analysis preloaded

hol.complex: hol.sh make-checkpoint.sh                                  \
     Multivariate/make.ml                                            \
     Library/card.ml Library/permutations.ml Library/products.ml     \
     Library/floor.ml Multivariate/misc.ml Library/iter.ml           \
     Multivariate/metric.ml Multivariate/vectors.ml                  \
     Multivariate/determinants.ml Multivariate/topology.ml           \
     Multivariate/convex.ml Multivariate/paths.ml                    \
     Multivariate/polytope.ml Multivariate/degree.ml                 \
     Multivariate/derivatives.ml Multivariate/clifford.ml            \
     Multivariate/integration.ml Multivariate/measure.ml             \
     Multivariate/multivariate_database.ml                           \
     Library/binomial.ml Multivariate/complexes.ml                   \
     Multivariate/canal.ml Multivariate/transcendentals.ml           \
     Multivariate/realanalysis.ml Multivariate/moretop.ml            \
     Multivariate/cauchy.ml Multivariate/complex_database.ml         \
     update_database.ml;                                             \
     if test `uname` = Linux; then                                   \
     ./make-checkpoint.sh hol.complex "loadt \"Multivariate/make.ml\"; loadt \"update_database.ml\"; loadt \"Multivariate/complexes.ml\"; loadt \"Multivariate/canal.ml\"; loadt \"Multivariate/transcendentals.ml\"; loadt \"Multivariate/realanalysis.ml\"; loadt \"Multivariate/cauchy.ml\"; loadt \"Multivariate/complex_database.ml\"; loadt \"update_database.ml\""; \
     else                                                           \
     echo '******************************************************'; \
     echo 'FAILURE: Image build assumes Linux and DMTCP';           \
     echo '******************************************************'; \
     fi

# Build all those
all: hol.sh hol hol.multivariate hol.sosa hol.card hol.complex;

# Build binaries and copy them to binary directory

install: hol.sh hol hol.multivariate hol.sosa hol.card hol.complex; cp hol hol.multivariate hol.sosa hol.card hol.complex ${BINDIR}

# Clean up all compiled files

clean:; \
  rm -rf bignum.c* bignum.o \
         update_database.ml pa_j.ml pa_j.cmi pa_j.cmo \
         hol_lib.a hol_lib.c* hol_lib.o hol_lib_inlined.ml \
         hol_loader.c* hol_loader.o \
         UnitTests/*_inlined.* UnitTests/*.byte UnitTests/*.native \
         ocaml-hol hol.sh hol hol.ckpt \
         hol.multivariate hol.multivariate.ckpt \
         hol.sosa hol.sosa.ckpt \
         hol.card hol.card.ckpt \
         hol.complex hol.complex.ckpt

# Also forget the configuration saved in config.mk

distclean: clean; rm -f $(CONFIG_FILE)

.PHONY: default switch switch-5 all install clean distclean FORCE
