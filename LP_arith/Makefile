CDDLIBPATH=/usr/lib/x86_64-linux-gnu
CDDINCLUDEPATH=/usr/include/cdd

GXX = g++
CC = $(GXX)
CCLD = $(CC)


.SUFFIXES: .c .o

COMPILE = $(CC) -O2 -DHAVE_LIBGMP=1 -DGMPRATIONAL -I. -I$(CDDLIBPATH) -I$(CDDINCLUDEPATH)

LINK = $(CCLD) $(AM_CFLAGS) $(CFLAGS) $(AM_LDFLAGS) $(LDFLAGS) -o $@

.c.o:
	$(COMPILE) -c `test -f '$<' || echo ''`$<

all: cdd_cert

cdd_cert: cdd_cert.o
	$(LINK) cdd_cert.o $(CDDLIBPATH)/libcddgmp.so -l gmp

clean:
	rm -f *~ *.o cdd_cert cdd_cert.exe
