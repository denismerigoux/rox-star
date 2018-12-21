# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

include $(FSTAR_HOME)/ulib/ml/Makefile.include

%.fst.hints: .%fst
	$(FSTAR) $^ --use_hints --record_hints --include ../ --include src-fstar/

%.exe: %.fst
	mkdir -p target/ocaml
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --codegen OCaml --lax  --odir target/ocaml \
	  	--include ../ --include src-fstar $^
	$(OCAMLOPT) -I target/ocaml/ target/ocaml/Rust.ml target/ocaml/BloomFilter.ml \
		target/ocaml/Spec_BloomFilter.ml target/ocaml/Test_BloomFilter.ml \
		-o Test_BloomFilter.exe

clean:
			rm src-fstar/BloomFilter.fst.hints

verify: src-fstar/BloomFilter.fst.hints


extract: src-fstar/Test.BloomFilter.exe

test: src-fstar/Test.BloomFilter.exe
	./Test_BloomFilter.exe
	cargo test
