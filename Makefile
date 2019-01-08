# Needs FSTAR_HOME to point to FStar's root directory

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

verify-bloom-filter:
	make -C bloom-filter/ verify

clean-bloom-filter:
	make -C bloom-filter/ clean

test-bloom-filter:
	make -C bloom-filter/ test

verify-textinput:
	make -C textinput/ verify

clean-textinput:
	make -C textinput/ clean

test-textinput:
	make -C textinput/ test

verify: verify-bloom-filter verify-textinput

clean: clean-bloom-filter clean-textinput

test: test-bloom-filter test-textinput

.PHONY: verify-bloom-filter verify-textinput
