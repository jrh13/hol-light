HOLLIGHT:=ocaml -init hol.ml

STANDALONE_EXAMPLES:=\
	Library/agm \
	Library/binary \
	Library/binomial \
	Examples/borsuk \
	Examples/brunn_minkowski \
	Library/card \
	Examples/combin \
	Examples/cong \
	Examples/cooper \
	Examples/dickson \
	Examples/dlo \
	Library/floor \
	Examples/forster \
	Examples/gcdrecurrence \
	Examples/harmonicsum \
	Examples/hol88 \
	Examples/holby \
	Library/integer \
	Examples/inverse_bug_puzzle_miz3 \
	Examples/inverse_bug_puzzle_tac \
	RichterHilbertAxiomGeometry/inverse_bug_puzzle_read \
	Library/isum \
	Examples/kb \
	Examples/lagrange_lemma \
	Examples/lucas_lehmer \
	Examples/mangoldt \
	Examples/mccarthy \
	Examples/misiurewicz \
	Examples/mizar \
	Library/multiplicative \
	Examples/multiwf \
	Examples/pell \
	Library/permutations \
	Library/primitive \
	Library/products \
	Examples/prog \
	Examples/prover9 \
	Library/q \
	Examples/rectypes \
	Examples/schnirelmann \
	Examples/solovay \
	Examples/sos \
	Examples/ste \
	Examples/sylvester_gallai \
	Examples/vitali \
	Library/wo \
	Library/analysis-transc \
	Library/prime-pratt \
	Library/prime-pocklington \
	Library/rstc-reduct

EXTENDED_EXAMPLES:=\
	Arithmetic/make \
	Boyer_Moore/make \
	Complex/make \
	IEEE/make \
	IsabelleLight/make \
	Jordan/make \
	Mizarlight/make \
	miz3/make-test \
	Minisat/make-taut \
	Model/make \
	Multivariate/make \
	Multivariate/make_complex \
	Ntrie/ntrie \
	Permutation/make \
	QBF/make \
	Quaternions/make \
	RichterHilbertAxiomGeometry/miz3/make \
	RichterHilbertAxiomGeometry/HilbertAxiom_read \
	Rqe/make \
	Unity/make \
	Multivariate/geom \
	Multivariate/tarski \
	Multivariate/cross \
	Multivariate/flyspeck \
	Multivariate/gamma \
	RichterHilbertAxiomGeometry/Topology \
	RichterHilbertAxiomGeometry/TarskiAxiomGeometry_read \
	Functionspaces/make \
	Formal_ineqs/make-ineqs

GREAT_100_THEOREMS:= \
	100/arithmetic_geometric_mean \
	100/arithmetic \
	100/ballot \
	100/bernoulli \
	100/bertrand-primerecip \
	100/birthday \
	100/cantor \
	100/cayley_hamilton \
	100/ceva \
	100/circle \
	100/chords \
	100/combinations \
	100/constructible \
	100/cosine \
	100/cubic \
	100/derangements \
	100/desargues \
	100/descartes \
	100/dirichlet \
	100/div3 \
	100/divharmonic \
	100/e_is_transcendental \
	100/euler \
	100/feuerbach \
	100/fourier \
	100/four_squares \
	100/friendship \
	100/fta \
	100/gcd \
	100/heron \
	100/inclusion_exclusion \
	100/independence \
	100/isosceles \
	100/konigsberg \
	100/lagrange \
	100/leibniz \
	100/lhopital \
	100/liouville \
	100/minkowski \
	100/morley \
	100/pascal \
	100/perfect \
	100/pick \
	100/piseries \
	100/platonic \
	100/pnt \
	100/polyhedron \
	100/ptolemy \
	100/pythagoras \
	100/quartic \
	100/ramsey \
	100/ratcountable \
	100/realsuncountable \
	100/reciprocity \
	100/stirling \
	100/subsequence \
	100/thales \
	100/triangular \
	100/two_squares \
	100/wilson


TESTS:=$(STANDALONE_EXAMPLES) $(EXTENDED_EXAMPLES) $(GREAT_100_THEOREMS)

LOGDIR:=/tmp/hollog_$(shell date '+%Y%m%d_%H%M')

LOGS:=$(patsubst %,$(LOGDIR)/%,$(TESTS))

all: $(TESTS)
	cat $(LOGS) > $(LOGDIR)/holtest.log


Library/analysis-transc:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Library/analysis.ml,/transc.ml,calc_real.ml,machin.ml,polylog.ml,poly.ml'
	@echo '### Loading Library/analysis.ml,/transc.ml,calc_real.ml,machin.ml,polylog.ml,poly.ml' > $(LOGDIR)/$@
	@(echo 'loadt "Library/analysis.ml";;'; echo 'loadt "Library/transc.ml";;'; \
		echo 'loadt "Library/calc_real.ml";;'; echo 'loadt "Examples/machin.ml";;'; \
		echo 'loadt "Examples/polylog.ml";;'; echo 'loadt "Library/poly.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

Library/prime-pratt:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Library/prime.ml,pratt.ml'
	@echo '### Loading Library/prime.ml,pratt.ml' > $(LOGDIR)/$@
	@(echo 'loadt "Library/prime.ml";;'; echo 'loadt "Library/pratt.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

Library/prime-pocklington:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Library/prime.ml,pocklington.ml'
	@echo '### Loading Library/prime.ml,pocklington.ml' > $(LOGDIR)/$@
	@(echo 'loadt "Library/prime.ml";;'; echo 'loadt "Library/pocklington.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

Library/rstc-reduct:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Library/rstc.ml,reduct.ml'
	@echo '### Loading Library/rstc.ml,reduct.ml' > $(LOGDIR)/$@
	@(echo 'loadt "Library/rstc.ml";;'; echo 'loadt "Examples/reduct.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

miz3/make-test:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading miz3/make.ml, miz3/test.ml (twice)'
	@echo '### Loading miz3/make.ml, miz3/test.ml (twice)' > $(LOGDIR)/$@
	@(echo 'loadt "miz3/make.ml";;'; echo 'loadt "miz3/test.ml";;'; echo 'loadt "miz3/test.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

Minisat/make-taut:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Minisat/make.ml,Minisat/taut.ml'
	if which zchaff > /dev/null ; then \
		echo '### Loading Minisat/make.ml,Minisat/taut.ml' > $(LOGDIR)/$@ ; \
		(echo 'loadt "Minisat/make.ml";;'; echo 'loadt "Minisat/taut.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1 ; \
	else \
		echo '### Error: skip Minisat/make.ml, Minisat/taut.ml because zchaff is not available' > $(LOGDIR)/$@ ; \
	fi

Formal_ineqs/make-ineqs:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading Formal_ineqs/make.ml, examples.hl, examples_poly.hl, examples_flyspeck.hl' > $(LOGDIR)/$@
	@(echo 'loadt "Formal_ineqs/make.ml";;'; echo 'loadt "Formal_ineqs/examples.hl";;'; echo 'loadt "Formal_ineqs/examples_poly.hl";;'; echo 'loadt "Formal_ineqs/examples_flyspeck.hl";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

100/bertrand-primerecip:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading 100/bertrand.ml,100/primerecip.ml'
	@echo '### Loading 100/bertrand.ml,100/primerecip.ml' > $(LOGDIR)/$@
	@(echo 'loadt "100/bertrand.ml";;'; echo 'loadt "100/primerecip.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1

%:
	@mkdir -p $(LOGDIR)/$$(dirname $@)
	@echo '### Loading $@.ml'
	@echo '### Loading $@.ml' > $(LOGDIR)/$@
	@echo 'loadt "$@.ml";;' | (time $(HOLLIGHT)) >> $(LOGDIR)/$@ 2>&1
