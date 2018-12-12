# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

verify-bloom-filter:
	make -C bloom-filter/ verify

verify-textinput:
	make -C textinput/ verify

verify: verify-bloom-filter verify-textinput

.PHONY: verify-bloom-filter verify-textinput
