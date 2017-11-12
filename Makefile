#############################################################################

COQC = coqc -I .
COQDEP = coqdep

FILES = \
	LibTactics \
        ListFacts \
	Terms \
	Perm \
	Disagr \
	Tuples \
	Fresh \
        Alpha_Equiv \
	Equiv \
	Equiv_Tuples \
        AACC_Equiv \
        C_Equiv \
        Problems \
        Substs \
        C_Unif \
        Termination \
        Soundness \
        Completeness

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
	rm -f *.aux *.vo .depend *.glob *.v# *.v~

.v.vo : .depend
	$(COQC) $<

.depend : $(VFILES)
	$(COQDEP) -I . $(VFILES) > .depend

include .depend

