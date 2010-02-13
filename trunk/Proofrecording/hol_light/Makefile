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

HOLSRC=sys.ml lib.ml type.ml term.ml thm.ml basics.ml nets.ml           \
       preterm.ml parser.ml printer.ml equal.ml bool.ml drule.ml        \
       tactics.ml itab.ml simp.ml theorems.ml ind-defs.ml class.ml      \
       trivia.ml canon.ml meson.ml quot.ml recursion.ml pair.ml         \
       num.ml arith.ml wf.ml calc_num.ml normalizer.ml grobner.ml       \
       ind-types.ml list.ml realax.ml calc_int.ml realarith.ml          \
       real.ml calc_rat.ml int.ml sets.ml iter.ml cart.ml define.ml     \
       help.ml database.ml

# Build the camlp4 syntax extension file (camlp5 for OCaml >= 3.10)

pa_j.cmo: sources pa_j.ml; if test `ocamlc -version | cut -c1-4` = "3.10" -o `ocamlc -version | cut -c1-4` = "3.11" ; \
                   then ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I +camlp5 pa_j.ml; \
                   else ocamlc -c -pp "camlp4r pa_extend.cmo q_MLast.cmo" -I +camlp4 pa_j.ml; \
                   fi

# Choose the source for the camlp4 syntax extension based on OCaml version
# If this doesn't work, pick the one for (or closest to) the major version
# of OCaml you're using.

pa_j.ml: pa_j_3.04.ml pa_j_3.06.ml pa_j_3.07.ml pa_j_3.08.ml pa_j_3.09.ml pa_j_3.10.ml; cp pa_j_`ocamlc -version | cut -c1-4`.ml pa_j.ml || cp pa_j_3.10.ml pa_j.ml

# Copy over and modify the sources

sources:; cp ../../*.ml .; \
          cp -f ../diffs/*.ml .; \
          java -jar ../tools/nametheorems.jar *.ml; \
          rm *.ml.old

# Build a standalone hol image called "hol" (needs Linux and ckpt program)

hol: pa_j.cmo ${HOLSRC} Examples/update_database.ml;                    \
     if test `uname` = Linux; then                                      \
     echo -e '#use "make.ml";;\nloadt "Examples/update_database.ml";;\nself_destruct "";;' | ckpt -a SIGUSR1 -n hol.snapshot ocaml;\
     mv hol.snapshot hol;                                               \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and ckpt program';        \
     echo '******************************************************';     \
     fi

# Build an image with multivatiate calculus preloaded.

hol.multivariate: ./hol                                                 \
     Multivariate/misc.ml Multivariate/vectors.ml                       \
     Multivariate/determinants.ml Multivariate/topology.ml              \
     Multivariate/convex.ml Multivariate/dimension.ml                   \
     Multivariate/analysis.ml Multivariate/clifford.ml                  \
     Multivariate/integration.ml Multivariate/measure.ml                \
     Multivariate/multivariate_database.ml Examples/update_database.ml; \
     echo -e 'loadt "Multivariate/make.ml";;\nloadt "Examples/update_database.ml";;\nself_destruct "Preloaded with multivariate analysis";;' | ./hol; mv hol.snapshot hol.multivariate;

# Build an image with analysis and SOS procedure preloaded

hol.sosa: ./hol                                                         \
     Examples/analysis.ml Examples/transc.ml                            \
     Examples/sos.ml Examples/update_database.ml;                       \
     echo -e 'loadt "Examples/analysis.ml";;\nloadt "Examples/transc.ml";;\nloadt "Examples/sos.ml";;\nloadt "Examples/update_database.ml";;\nself_destruct "Preloaded with analysis and SOS";;' | ./hol; mv hol.snapshot hol.sosa;

# Build an image with cardinal arithmetic preloaded

hol.card: ./hol Examples/card.ml; Examples/update_database.ml;          \
        echo -e 'loadt "Examples/card.ml";;\nloadt "Examples/update_database.ml";;\nself_destruct "Preloaded with cardinal arithmetic";;' | ./hol; mv hol.snapshot hol.card;

# Build an image with multivariate-based complex analysis preloaded

hol.complex: ./hol.multivariate                                         \
        Multivariate/complex.ml Multivariate/canal.ml                   \
        Multivariate/transc.ml Multivariate/real.ml                     \
        Multivariate/cauchy.ml Multivariate/complex_database.ml         \
        Examples/update_database.ml;                                    \
        echo -e 'loadt "Multivariate/complex.ml";;\nloadt "Multivariate/canal.ml";;\nloadt "Multivariate/transc.ml";;\nloadt "Multivariate/real.ml";;\nloadt "Multivariate/cauchy.ml";;\nloadt "Multivariate/complex_database.ml";;\nloadt "Examples/update_database.ml";;\nself_destruct "Preloaded with multivariate-based complex analysis";;' | ./hol.multivariate; mv hol.snapshot hol.complex;

# Build all those

all: hol hol.multivariate hol.sosa hol.card hol.complex;

# Build binaries and copy them to binary directory

install: hol hol.multivariate hol.sosa hol.card hol.complex; cp hol hol.multivariate hol.sosa hol.card hol.complex ${BINDIR}

# Clean up all compiled files

clean:; rm -f *.ml *.ml.old pa_j.cmi pa_j.cmo hol hol.multivariate hol.sosa hol.card hol.complex;
