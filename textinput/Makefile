# Needs FSTAR_HOME to point to FStar's root directory


FSTAR=$(FSTAR_HOME)/bin/fstar.exe

include $(FSTAR_HOME)/ulib/ml/Makefile.include

%.fst.hints: %.fst
	$(FSTAR) $^ --record_hints --use_hints  --include ../

%.exe: %.fst
	mkdir -p target/ocaml
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --codegen OCaml --lax  --odir target/ocaml \
	  --include ../ --include src-fstar $^
	$(OCAMLOPT) -I target/ocaml/ target/ocaml/Rust.ml target/ocaml/TextInput.ml \
		target/ocaml/Test_TextInput.ml -o Test_TextInput.exe
clean:
	rm src-fstar/TextInput.fst.hints

verify: src-fstar/TextInput.fst.hints

extract: src-fstar/Test.TextInput.exe

test : src-fstar/Test.TextInput.exe
	./Test_TextInput.exe
	cargo test
