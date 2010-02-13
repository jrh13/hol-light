# Thanks to Carl Witty for 3.07 and 3.08 ports of pa_j.ml and this make procedure

OCAMLC=ocamlc -dtypes -g -pp "camlp4o ./init.cmo ./pa_j.cmo" -I +campl4  nums.cma unix.cma

CAMLP4O=camlp4o ./init.cmo ./pa_j.cmo

pa_j.cmo: pa_j.ml; ocamlc -c -pp 'camlp4r pa_extend.cmo q_MLast.cmo' -I `which camlp4 | sed -e 's/bin\/camlp4/lib\/ocaml\/camlp4/'` pa_j.ml

pa_j.ml: pa_j_3.04.ml pa_j_3.06.ml pa_j_3.07+2.ml; cp pa_j_`ocamlc -version`.ml pa_j.ml

clean:; rm -f pa_j.ml pa_j.cmi pa_j.cmo


init.cmo : init.ml
	ocamlc -I +camlp4 -c ./init.ml

core.out : srccore init.cmo pa_j.cmo
	$(OCAMLC) -o core.out core.ml

srccore :;
	cat startcore.ml > core.ml
	cat lib.ml >> core.ml
	cat lib2.ml >> core.ml
	cat type.ml >> core.ml
	cat term.ml >> core.ml
	cat proofobjects_init.ml >> core.ml
	cat proofobjects_dummy.ml >> core.ml
	cat thm.ml >> core.ml
	cat basics.ml >> core.ml
	cat nets.ml >> core.ml
	cat preterm.ml >> core.ml
	cat parser.ml >> core.ml
	cat printer.ml >> core.ml
	cat equal.ml >> core.ml
	cat bool.ml >> core.ml
	cat drule.ml >> core.ml
	cat tactics.ml >> core.ml
	cat itab.ml >> core.ml
	cat simp.ml >> core.ml
	cat theorems.ml >> core.ml
	cat ind-defs.ml >> core.ml
	cat class.ml >> core.ml
	cat trivia.ml >> core.ml
	cat canon.ml >> core.ml
	cat meson.ml >> core.ml
	cat quot.ml >> core.ml
	cat recursion.ml >> core.ml
	cat pair.ml >> core.ml
	cat num.ml >> core.ml
	cat arith.ml >> core.ml
	cat wf.ml >> core.ml
	cat calc_num.ml >> core.ml
	cat normalizer.ml >> core.ml
	cat grobner.ml >> core.ml
	cat ind-types.ml >> core.ml
	cat list.ml >> core.ml
	cat realax.ml >> core.ml
	cat calc_int.ml >> core.ml
	cat realarith.ml >> core.ml
	cat real.ml >> core.ml
	cat calc_rat.ml >> core.ml
	cat int.ml >> core.ml
	cat sets.ml >> core.ml
	cat Examples/analysis.ml >> core.ml
	cat Examples/transc.ml >> core.ml
	cat Complex/complex.ml >> core.ml
	cat Complex/cpoly.ml >> core.ml
	cat Complex/fundamental.ml >> core.ml
	cat Complex/quelim.ml >> core.ml
	cat Complex/polyconv.ml >> core.ml
	cat Complex/grobner.ml >> core.ml
	cat Complex/real.ml >> core.ml

srcexamples:;
	cat Complex/quelim_examples.ml >> core.ml
	cat Examples/binomial.ml >> core.ml
	cat Examples/wo.ml >> core.ml
	cat Examples/card.ml >> core.ml
	cat Examples/cong.ml >> core.ml
	cat Examples/cooper.ml >> core.ml
	cat Examples/floor.ml >> core.ml
	cat Examples/forster.ml >> core.ml
	cat Examples/lagrange.ml >> core.ml
	cat Examples/mccarthy.ml >> core.ml
	cat Examples/multivariate.ml >> core.ml
	cat Examples/multiwf.ml >> core.ml
	cat Examples/prime.ml >> core.ml
	cat Examples/pell.ml >> core.ml
	cat Examples/poly.ml >> core.ml
	cat Examples/polylog.ml >> core.ml
	cat Examples/rectypes.ml >> core.ml
	cat Examples/rstc.ml >> core.ml
	cat Examples/reduct.ml >> core.ml

