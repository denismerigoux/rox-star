# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

%.fst.hints: %.fst
	$(FSTAR) $^ --record_hints --use_hints  --include ../


verify: TextInput.fst.hints