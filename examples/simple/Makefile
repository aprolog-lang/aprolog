
EXAMPLES = bi cps cut dcg debruijn defns diff dl esubst fol ill infix \
	   lam lambda-mu lam-ref ltal miniml nl nomu nsl picalc spi systemf \
           unify zeta
APLS = $(addsuffix .apl, $(EXAMPLES))
OUTS = $(addsuffix .out, $(EXAMPLES))
OLDS = $(addsuffix .old, $(EXAMPLES))
DIFFS = $(addsuffix .diff, $(EXAMPLES))

ifndef APROLOG
APROLOG = ../../bin/aprolog -q $(AFLAGS)
endif

all : $(OUTS)

old : $(OLDS) 
%.out : %.apl
	$(APROLOG) $< > $@

%.old : %.apl
	$(APROLOG) $< > $@

clean : 
	rm -rf $(OUTS)

diff : $(DIFFS) 

%.diff : %.out 
	diff $< $*.old > $@
