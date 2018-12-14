# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

%.fst:
	$(FSTAR) $^ --use_hints --record_hints --include ../ --include src-fstar/

all: verify cargo

verify:
		$(FSTAR) src-fstar/Proof.BloomFilter.fst --use_hints --record_hints --include ../ --include src-fstar/

cargo:
		cargo test
