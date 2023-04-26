# The hull_light.ml file can be freshly generated from the Sage script,
# using the first (default) Makefile target, while "clobber" removes
# it so that it needs to be regenerated.

.PHONY: clean clobber

hull_light.ml: hull-light-20230416.sage; sage hull-light-20230416.sage >hull_light.ml

clean:; rm -f *.sage.py

clobber:; rm -f hull-light-20230416.sage.py hull_light.ml
