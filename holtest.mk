HOLLIGHT:=./hol.sh

STANDALONE_EXAMPLES:=\
	Library/agm \
	Library/bdd \
	Examples/bdd_examples \
	Library/binary \
	Library/binomial \
	Examples/bitblast \
	Examples/bitblast_generic \
	Library/bitmatch \
	Library/bitsize \
	Examples/bondy \
	Examples/borsuk \
	Examples/brunn_minkowski \
	Library/card \
	Examples/combin \
	Examples/complexpolygon \
	Examples/cong \
	Examples/cooper \
	Examples/dickson \
	Examples/digit_serial_methods \
	Examples/division_algebras \
	Examples/dlo \
	Library/fieldtheory \
	Library/floor \
	Examples/forster \
	Examples/gcdrecurrence \
	Library/grouptheory \
	Examples/harmonicsum \
	Examples/hol88 \
	Examples/holby \
	Library/integer \
	Examples/inverse_bug_puzzle_miz3 \
	Examples/inverse_bug_puzzle_tac \
	RichterHilbertAxiomGeometry/inverse_bug_puzzle_read \
	Library/isum \
	Library/jacobi \
	Examples/kb \
	Examples/lagrange_lemma \
	Examples/lucas_lehmer \
	Examples/mangoldt \
	Library/matroids \
	Examples/mccarthy \
	Examples/miller_rabin \
	Examples/misiurewicz \
	Examples/mizar \
	Library/modmul_group \
	Library/multiplicative \
	Examples/multiwf \
	Examples/padics \
	Examples/pell \
	Library/permutations \
	Library/primitive \
	Library/products \
	Examples/prog \
	Examples/prover9 \
	Examples/pseudoprime \
	Library/q \
	Library/rabin_test \
	Examples/rectypes \
	Library/ringtheory \
	Examples/safetyliveness \
	Examples/schnirelmann \
	Examples/solovay \
	Examples/sos \
	Examples/ste \
	Examples/sylvester_gallai \
	Examples/vitali \
	Library/wo \
	Library/words \
	Library/word_automata \
	Examples/zolotarev \
	Library/analysis-transc \
	Library/prime-pratt \
	Library/prime-pocklington \
	Library/rstc-reduct

EXTENDED_EXAMPLES:=\
	Arithmetic/make \
	Boyer_Moore/make \
	Cadical/make-test \
	Complex/make \
	Divstep/make \
	EC/make \
	GL/make \
	Geometric_Algebra/make \
	IEEE/make \
	IsabelleLight/make \
	Jordan/make \
	Logic/make \
	Mizarlight/make \
	miz3/make-test \
	Minisat/make-test \
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
	Multivariate/cross \
	Multivariate/cvectors \
	Multivariate/flyspeck \
	Multivariate/gamma \
	Multivariate/geom \
	Multivariate/homology \
	Multivariate/lpspaces \
	Multivariate/msum \
	Multivariate/paracompact \
	Multivariate/specialtopologies \
	Multivariate/tarski \
	RichterHilbertAxiomGeometry/Topology \
	RichterHilbertAxiomGeometry/TarskiAxiomGeometry_read \
	Functionspaces/make \
	Formal_ineqs/make-ineqs \
	TacticTrace/make-test

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
	100/isoperimetric \
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
	100/transcendence \
	100/triangular \
	100/two_squares \
	100/wilson


TESTS:=$(STANDALONE_EXAMPLES) $(EXTENDED_EXAMPLES) $(GREAT_100_THEOREMS)

LOGDIR:=/tmp/hol-light-test

LOGS:=$(patsubst %,$(LOGDIR)/%,$(TESTS))

READY:=$(patsubst %,%.ready,$(LOGS))

all: $(READY)
	cat $(LOGS) > $(LOGDIR)/holtest.log

$(LOGDIR)/Library/analysis-transc.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Library/analysis-transc)
	@echo '### Loading Library/analysis.ml,/transc.ml,calc_real.ml,machin.ml,polylog.ml,poly.ml'
	@echo '### Loading Library/analysis.ml,/transc.ml,calc_real.ml,machin.ml,polylog.ml,poly.ml' > $(LOGDIR)/Library/analysis-transc
	@(echo 'loadt "Library/analysis.ml";;'; echo 'loadt "Library/transc.ml";;'; \
		echo 'loadt "Library/calc_real.ml";;'; echo 'loadt "Examples/machin.ml";;'; \
		echo 'loadt "Examples/polylog.ml";;'; echo 'loadt "Library/poly.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Library/analysis-transc 2>&1
	@touch $(LOGDIR)/Library/analysis-transc.ready

$(LOGDIR)/Library/prime-pratt.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Library/prime-pratt)
	@echo '### Loading Library/prime.ml,pratt.ml'
	@echo '### Loading Library/prime.ml,pratt.ml' > $(LOGDIR)/Library/prime-pratt
	@(echo 'loadt "Library/prime.ml";;'; echo 'loadt "Library/pratt.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Library/prime-pratt 2>&1
	@touch $(LOGDIR)/Library/prime-pratt.ready

$(LOGDIR)/Library/prime-pocklington.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Library/prime-pocklington)
	@echo '### Loading Library/prime.ml,pocklington.ml'
	@echo '### Loading Library/prime.ml,pocklington.ml' > $(LOGDIR)/Library/prime-pocklington
	@(echo 'loadt "Library/prime.ml";;'; echo 'loadt "Library/pocklington.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Library/prime-pocklington 2>&1
	@touch $(LOGDIR)/Library/prime-pocklington.ready

$(LOGDIR)/Library/rstc-reduct.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Library/rstc-reduct)
	@echo '### Loading Library/rstc.ml,reduct.ml'
	@echo '### Loading Library/rstc.ml,reduct.ml' > $(LOGDIR)/Library/rstc-reduct
	@(echo 'loadt "Library/rstc.ml";;'; echo 'loadt "Examples/reduct.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Library/rstc-reduct 2>&1
	@touch $(LOGDIR)/Library/rstc-reduct.ready

$(LOGDIR)/miz3/make-test.ready:
	@mkdir -p $(LOGDIR)/$$(dirname miz3/make-test)
	@echo '### Loading miz3/make.ml, miz3/test.ml (twice)'
	@echo '### Loading miz3/make.ml, miz3/test.ml (twice)' > $(LOGDIR)/miz3/make-test
	@(echo 'loadt "miz3/make.ml";;'; echo 'loadt "miz3/test.ml";;'; echo 'loadt "miz3/test.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/miz3/make-test 2>&1
	@touch $(LOGDIR)/miz3/make-test.ready

$(LOGDIR)/Minisat/make-test.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Minisat/make-test)
	@echo '### Loading Minisat/make.ml,Minisat/test.ml'
	if which zchaff > /dev/null ; then \
		echo '### Loading Minisat/make.ml,Minisat/test.ml' > $(LOGDIR)/Minisat/make-test ; \
		(echo 'loadt "Minisat/make.ml";;'; echo 'loadt "Minisat/taut.ml";;'; echo 'loadt "Minisat/test.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Minisat/make-test 2>&1 ; \
	else \
		echo '### Error: skip Minisat/make.ml, Minisat/test.ml because zchaff is not available' > $(LOGDIR)/Minisat/make-test ; \
	fi
	@touch $(LOGDIR)/Minisat/make-test.ready

$(LOGDIR)/Formal_ineqs/make-ineqs.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Formal_ineqs/make-ineqs)
	@echo '### Loading Formal_ineqs/make.ml, examples.hl, examples_poly.hl, examples_flyspeck.hl' > $(LOGDIR)/Formal_ineqs/make-ineqs
	@(echo 'loadt "Formal_ineqs/make.ml";;'; echo 'loadt "Formal_ineqs/examples.hl";;'; echo 'loadt "Formal_ineqs/examples_poly.hl";;'; echo 'loadt "Formal_ineqs/examples_flyspeck.hl";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Formal_ineqs/make-ineqs 2>&1
	@touch $(LOGDIR)/Formal_ineqs/make-ineqs.ready

$(LOGDIR)/100/bertrand-primerecip.ready:
	@mkdir -p $(LOGDIR)/$$(dirname 100/bertrand-primerecip)
	@echo '### Loading 100/bertrand.ml,100/primerecip.ml'
	@echo '### Loading 100/bertrand.ml,100/primerecip.ml' > $(LOGDIR)/100/bertrand-primerecip
	@(echo 'loadt "100/bertrand.ml";;'; echo 'loadt "100/primerecip.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/100/bertrand-primerecip 2>&1
	@touch $(LOGDIR)/100/bertrand-primerecip.ready

$(LOGDIR)/Cadical/make-test.ready:
	@mkdir -p $(LOGDIR)/$$(dirname Cadical/make-test)
	@echo '### Loading Cadical/make.ml,Cadical/test.ml'
	if which cadical > /dev/null ; then \
		echo '### Loading Cadical/make.ml,Cadical/test.ml' > $(LOGDIR)/Cadical/make-test ; \
		(echo 'loadt "Cadical/make.ml";;'; echo 'loadt "Minisat/taut.ml";;'; echo 'loadt "Cadical/test.ml";;') | (time $(HOLLIGHT)) >> $(LOGDIR)/Cadical/make-test 2>&1 ; \
	else \
		echo '### Error: skip Cadical/make.ml, Cadical/test.ml because cadical is not available' > $(LOGDIR)/Cadical/make-test ; \
	fi
	@touch $(LOGDIR)/Cadical/make-test.ready

$(LOGDIR)/TacticTrace/make-test.ready:
	@mkdir -p $(LOGDIR)/$$(dirname TacticTrace/make-test)
	@echo '### Running TacticTrace/Makefile'
	@$(MAKE) clean --quiet -C TacticTrace
	@$(MAKE) --quiet -C TacticTrace
	@cd TacticTrace && ./build-hol-kernel.sh
	@$(MAKE) test --quiet -C TacticTrace > $(LOGDIR)/TacticTrace/make-test 2>&1
	@cat TacticTrace/examples/*.hollog >> $(LOGDIR)/TacticTrace/make-test
	@touch $(LOGDIR)/TacticTrace/make-test.ready

# Recall that $* is the stem matched by the %
$(LOGDIR)/%.ready:
	@mkdir -p $(LOGDIR)/$$(dirname $*)
	@echo '### Loading $*.ml'
	@echo '### Loading $*.ml' > $(LOGDIR)/$*
	@echo 'loadt "$*.ml";;' | (time $(HOLLIGHT)) >> $(LOGDIR)/$* 2>&1
	@touch $(LOGDIR)/$*.ready
