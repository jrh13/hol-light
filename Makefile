###############################################################################
# Makefile for HOL Light                                                      #
#                                                                             #
# Simple "make" just builds the camlp4 syntax extension "pa_j.cmo", which is  #
# necessary to load the HOL Light core into the OCaml toplevel.               #
#                                                                             #
# The later options such as "make hol" create standalone images, but only     #
# work under Linux when the "ckpt" checkpointing program is installed.        #
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
       canon.ml meson.ml metis.ml quot.ml recursion.ml pair.ml          \
       nums.ml arith.ml wf.ml calc_num.ml normalizer.ml grobner.ml      \
       ind_types.ml lists.ml realax.ml calc_int.ml realarith.ml         \
       real.ml calc_rat.ml int.ml sets.ml iterate.ml cart.ml define.ml  \
       help.ml database.ml update_database.ml

# Some parameters to help decide how to build things

OCAML_VERSION=`ocamlc -version | cut -c1-4`
OCAML_BINARY_VERSION=`ocamlc -version | cut -c1-3`
CAMLP5_BINARY_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -c1`
CAMLP5_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -f1-3 -d'.' | cut -c1-6`

# Build the camlp4 syntax extension file (camlp5 for OCaml >= 3.10)

pa_j.cmo: pa_j.ml; if test ${OCAML_BINARY_VERSION} = "3.0" ; \
                   then ocamlc -c -pp "camlp4r pa_extend.cmo q_MLast.cmo" -I `camlp4 -where` pa_j.ml ; \
                   else if test ${OCAML_BINARY_VERSION} = "3.1" -o ${OCAML_VERSION} = "4.00" -o ${OCAML_VERSION} = "4.01"  -o ${OCAML_VERSION} = "4.02" -o ${OCAML_VERSION} = "4.03" -o ${OCAML_VERSION} = "4.04" ; \
                        then  ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` pa_j.ml ; \
                        else ocamlc -safe-string -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` pa_j.ml ; \
                        fi \
                   fi

# Choose an appropriate camlp4 or camlp5 syntax extension.
#
# For OCaml < 3.10 (OCAML_BINARY_VERSION = "3.0"), this uses the built-in
# camlp4, and in general there are different versions for each OCaml version
#
# For OCaml >= 3.10 (OCAML_BINARY_VERSION = "3.1" or "4.x"), this uses the
# separate program camlp5. Now the appropriate syntax extensions is determined
# based on the camlp5 version. The main distinction is < 6.00 and >= 6.00, but
# there are some other incompatibilities, unfortunately.

pa_j.ml: pa_j_3.07.ml pa_j_3.08.ml pa_j_3.09.ml pa_j_3.1x_5.xx.ml pa_j_3.1x_6.xx.ml; \
        if test ${OCAML_BINARY_VERSION} = "3.0"  ; \
        then cp pa_j_${OCAML_VERSION}.ml pa_j.ml ; \
        else if test ${CAMLP5_VERSION} = "6.02.1" ; \
             then cp pa_j_3.1x_6.02.1.ml pa_j.ml; \
             else if test ${CAMLP5_VERSION} = "6.02.2" -o ${CAMLP5_VERSION} = "6.02.3" -o ${CAMLP5_VERSION} = "6.03" -o ${CAMLP5_VERSION} = "6.04" -o ${CAMLP5_VERSION} = "6.05" -o ${CAMLP5_VERSION} = "6.06" ; \
                  then cp pa_j_3.1x_6.02.2.ml pa_j.ml; \
                  else if test ${CAMLP5_VERSION} = "6.06" -o ${CAMLP5_VERSION} = "6.07" -o ${CAMLP5_VERSION} = "6.08" -o ${CAMLP5_VERSION} = "6.09" -o ${CAMLP5_VERSION} = "6.10" -o ${CAMLP5_VERSION} = "6.11" -o ${CAMLP5_VERSION} = "6.12" -o ${CAMLP5_VERSION} = "6.13" -o ${CAMLP5_VERSION} = "6.14" -o ${CAMLP5_VERSION} = "6.15" -o ${CAMLP5_VERSION} = "6.16" -o ${CAMLP5_VERSION} = "6.17" ; \
                       then cp pa_j_3.1x_6.11.ml pa_j.ml; \
                       else cp pa_j_3.1x_${CAMLP5_BINARY_VERSION}.xx.ml pa_j.ml; \
                       fi \
                  fi \
             fi \
        fi

# Build a standalone hol image called "hol" (needs Linux and ckpt program)

hol: pa_j.cmo ${HOLSRC} update_database.ml;                    \
     if test `uname` = Linux; then                                      \
     echo -e '#use "make.ml";;\nloadt "update_database.ml";;\nself_destruct "";;' | ckpt -a SIGUSR1 -n hol.snapshot ocaml;\
     mv hol.snapshot hol;                                               \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and ckpt program';        \
     echo '******************************************************';     \
     fi

# Build an image with multivariate calculus preloaded.

hol.multivariate: ./hol                                                 \
     Library/card.ml Library/permutations.ml Library/products.ml        \
     Library/floor.ml Multivariate/misc.ml Library/iter.ml              \
     Multivariate/metric.ml Multivariate/vectors.ml                     \
     Multivariate/determinants.ml Multivariate/topology.ml              \
     Multivariate/convex.ml Multivariate/paths.ml                       \
     Multivariate/polytope.ml Multivariate/degree.ml                    \
     Multivariate/derivatives.ml Multivariate/clifford.ml               \
     Multivariate/integration.ml Multivariate/measure.ml                \
     Multivariate/multivariate_database.ml update_database.ml;          \
     echo -e 'loadt "Multivariate/make.ml";;\nloadt "update_database.ml";;\nself_destruct "Preloaded with multivariate analysis";;' | ./hol; mv hol.snapshot hol.multivariate;

# Build an image with analysis and SOS procedure preloaded

hol.sosa: ./hol                                                         \
     Library/analysis.ml Library/transc.ml                              \
     Examples/sos.ml update_database.ml;                                \
     echo -e 'loadt "Library/analysis.ml";;\nloadt "Library/transc.ml";;\nloadt "Examples/sos.ml";;\nloadt "update_database.ml";;\nself_destruct "Preloaded with analysis and SOS";;' | ./hol; mv hol.snapshot hol.sosa;

# Build an image with cardinal arithmetic preloaded

hol.card: ./hol Library/card.ml; update_database.ml;                    \
        echo -e 'loadt "Library/card.ml";;\nloadt "update_database.ml";;\nself_destruct "Preloaded with cardinal arithmetic";;' | ./hol; mv hol.snapshot hol.card;

# Build an image with multivariate-based complex analysis preloaded

hol.complex: ./hol.multivariate                                         \
        Library/binomial.ml Multivariate/complexes.ml                   \
        Multivariate/canal.ml Multivariate/transcendentals.ml           \
        Multivariate/realanalysis.ml Multivariate/moretop.ml            \
        Multivariate/cauchy.ml Multivariate/complex_database.ml         \
        update_database.ml;                                             \
        echo -e 'loadt "Multivariate/complexes.ml";;\nloadt "Multivariate/canal.ml";;\nloadt "Multivariate/transcendentals.ml";;\nloadt "Multivariate/realanalysis.ml";;\nloadt "Multivariate/cauchy.ml";;\nloadt "Multivariate/complex_database.ml";;\nloadt "update_database.ml";;\nself_destruct "Preloaded with multivariate-based complex analysis";;' | ./hol.multivariate; mv hol.snapshot hol.complex;

# Build all those

all: hol hol.multivariate hol.sosa hol.card hol.complex;

# Build binaries and copy them to binary directory

install: hol hol.multivariate hol.sosa hol.card hol.complex; cp hol hol.multivariate hol.sosa hol.card hol.complex ${BINDIR}

# Clean up all compiled files

clean:; rm -f pa_j.ml pa_j.cmi pa_j.cmo hol hol.multivariate hol.sosa hol.card hol.complex;
