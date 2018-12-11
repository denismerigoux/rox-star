# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

verify-bloom:
	make -C bloom-filter/ verify

verify: verify-bloom
