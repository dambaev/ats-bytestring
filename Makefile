######
#
# Note that
# certain installations require the following changes:
#
# atscc -> patscc
# atsopt -> patsopt
# ATSHOME -> PATSHOME
#
######
#
#
######
#
ATSHOME=$(shell dirname $(shell dirname $(shell readlink $(shell which patscc))))
ATSCC=patscc
ATSOPT=patsopt
#
ATSCCFLAGS=-O2 -DATS_MEMALLOC_LIBC -I"../libs/"
ATSLIBS=
# ATSCCFLAGS=-O2
#
# '-flto' enables link-time optimization such as inlining lib functions
#
# ATSCCFLAGS=-O2 -flto
#
#
ATS_TEST_DATS=\
	TEST/test1.dats \
	TEST/test2.dats \
	TEST/test3.dats \
	TEST/test4.dats
ATS_DATS=DATS/bytestring_flat.dats
ATS_SATS=SATS/bytestring.sats
######
#

ATS_OBJS= $(ATS_SATS:.sats=_sats.o) $(ATS_DATS:.dats=_dats.o)
ATS_TEST_OBJS= $(ATS_OBJS) $(ATS_TEST_DATS:.dats=_dats.o)

.PHONY: all clean

all: test

cleanall::
#
######
#
# Please uncomment the following three lines and replace the name [foo]
# with the name of the file you want to compile
#


test: $(ATS_TEST_OBJS) \
		test1 \
		test2 \
		test3 \
		test4

test1: $(ATS_TEST_OBJS) ; \
   $(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/test1.dats $(ATSLIBS)
test2: $(ATS_TEST_OBJS) ; \
   $(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/test2.dats $(ATSLIBS)
test3: $(ATS_TEST_OBJS) ; \
   $(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/test3.dats $(ATSLIBS)
test4: $(ATS_TEST_OBJS) ; \
   $(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/test4.dats $(ATSLIBS)
cleanall:: ; $(RMF) test*
#
######
#
# You may find these rules useful
#
%_sats.o: %.sats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
%_dats.o: %.dats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
#
######
#
RMF=rm -f
#
######
#
clean:: ; $(RMF) test*
clean:: ; $(RMF) *~
clean:: ; find -name '*_?ats.o' -exec $(RMF) {} \;
clean:: ; find -name '*_?ats.c' -exec $(RMF) {} \;
#
cleanall:: clean
#
###### end of [Makefile] ######

