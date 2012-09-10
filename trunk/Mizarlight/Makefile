#
# Syntax extensions to support Mizar Light: new infix operators
#

# Build the camlp4 syntax extension file

pa_f.cmo: pa_f.ml; if test `ocamlc -version | cut -c1-3` = "3.0" ; \
                   then ocamlc -c -pp "camlp4r pa_extend.cmo q_MLast.cmo" -I +camlp4 pa_f.ml; \
                   else ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I +camlp5 pa_f.ml; \
                   fi

clean:; rm -f pa_f.cmi pa_f.cmo
