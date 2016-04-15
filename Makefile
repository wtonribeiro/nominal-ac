#############################################################################

COQC = coqc -I .
COQDEP = coqdep

FILES = \
	LibTactics \
	Terms \
	Perm \
	Disagr \
	Tuples \
	Fresh \
	w_Equiv \
        Alpha_Equiv \
	Equiv \
	Equiv_Tuples \
        AAC_Equiv 

all : main
pat: $(foreach i, $(PAT), $(i).vo)
core: $(foreach i, $(CORE), $(i).vo)

############################################################################

VFILES = $(foreach i, $(FILES), $(i).v)
VOFILES = $(foreach i, $(FILES), $(i).vo)

.PHONY: all clean default
.SUFFIXES: .v .vo

main : $(VOFILES)

lib : Metatheory.vo

clean :
	rm -f *.vo .depend

.v.vo : .depend
	$(COQC) $<

.depend : $(VFILES)
	$(COQDEP) -I . $(VFILES) > .depend

include .depend

