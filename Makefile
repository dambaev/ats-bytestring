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
ATS_DATS=DATS/bytestring_flat.dats
ATS_SATS=SATS/bytestring.sats
######
#

ATS_OBJS= $(ATS_SATS:.sats=_sats.o) $(ATS_DATS:.dats=_dats.o)

.PHONY: all clean

all: test

cleanall::
#
######
#
# Please uncomment the following three lines and replace the name [foo]
# with the name of the file you want to compile
#


test: \
		test26 \
		test25 \
		test24 \
		test23 \
		test22 \
		test21 \
		test20 \
		test19 \
		test18 \
		test1 \
		test2 \
		test3 \
		test4 \
		test5 \
		test6 \
		test7 \
		test8 \
		test9 \
		test10 \
		test11 \
		test12 \
		test13 \
		test14 \
		test15 \
		test16 \
		test17

test1: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test1.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test2: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test2.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test3: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test3.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test4: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test4.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test5: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test5.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test6: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test6.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test7: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test7.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test8: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test8.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test9: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test9.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test10: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test10.dats $(ATSLIBS) && exit 1 || touch test10
test11: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test11.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test12: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test12.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test13: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test13.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test14: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test14.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test15: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test15.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test16: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test16.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test17: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/test17.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test18: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test19: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test20: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test21: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test22: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test23: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test24: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test25: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
test26: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@_bin $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	./$@_bin
	@touch $@
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

