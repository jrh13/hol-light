# I assume a snapshot with hol.ml loaded was made using criu (which only works
# with Linux, sorry).
#
# You can create such a snapshot by following:
# 1. Start candle normally in a terminal
# 2. Manually load hol.ml using #use "hol.ml";;
# 3. Wait until loading is done
# 4. Make sure you are in the candle repositry, and an (empty) directory called
#    checkpoint exists (I am not sure whether it has to be empty, but just to
#    be sure...)
# 5. Run sudo criu dump -D checkpoint -t $(pidof cake) --shell-job
#    If you look at the terminal where Candle was running, it should have been
#    killed. If not, maybe you got the wrong cake process?
#
# criu might complain about a lack of capabilities. In that case, you should
# consult your preferred resources to find out how you can give those
# CAP_SYS_ADMIN to it.

# Since we need to restore into a terminal, but also want to call it via make
# we need to place it into a pseudoterminal. To avoid having to somehow pass
# the user password into that, we assume that criu can be run with sudo without
# a password.
#
# This can be achieved by:
# 1. Calling visudo
# 2. Adding
#    user ALL = (root) NOPASSWD: /usr/bin/criu
#    to it, taking care to replace user with the proper username.
#
# No claims are made on whether this a good idea in regards to security.

# The above procedure is a bit hacky, so if anyone knows a better way, please
# let me know.

# In some cases, Ctrl-C may not be enough to stop the tests. In that case,
# kill the process (for example using pkill cake).

# To rerun the tests, you need to remove the directory specified in LOGDIR
# (see below).

CANDLE:=python3 -c "import pty,sys; pty.spawn(['sudo','criu','restore','-D','checkpoint/','--shell-job'])"

GREAT_100_THEOREMS:= \
	100/arithmetic_geometric_mean \
	100/arithmetic \
	100/ballot \
	100/bernoulli \
	100/bertrand \
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
	100/isoperimetric \
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
	100/primerecip \
	100/ptolemy \
	100/pythagoras \
	100/quartic \
	100/ramsey \
	100/ratcountable \
	100/realsuncountable \
	100/reciprocity \
	100/sqrt \
	100/stirling \
	100/subsequence \
	100/thales \
	100/transcendence \
	100/triangular \
	100/two_squares \
	100/wilson

TESTS:=$(GREAT_100_THEOREMS)

LOGDIR:=/tmp/candle-test

LOGS:=$(patsubst %,$(LOGDIR)/%,$(TESTS))

READY:=$(patsubst %,%.ready,$(LOGS))

all: $(READY)
	cat $(LOGS) > $(LOGDIR)/candletest.log

$(LOGDIR)/%.ready:
	@mkdir -p $(LOGDIR)/$$(dirname $*)
	@echo '### Loading $*.ml'
	@echo '### Loading $*.ml' > $(LOGDIR)/$*
	@echo 'loads "$*.ml";;Runtime.exit 0;;' | (timeout 60 $(CANDLE) >> $(LOGDIR)/$* 2>&1) || echo "TIMEOUT" >> $(LOGDIR)/$*
	@touch $(LOGDIR)/$*.ready
