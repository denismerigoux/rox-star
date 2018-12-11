# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

%.fst.hints: %.fst
	$(FSTAR) $^ --use_hints --record_hints --include ../


verify: Proof.BloomFilter.fst.hints
