CHARON_EXE = charon
AENEAS_EXE = aeneas

AENEAS_OPTIONS ?= -loops-to-rec

.PHONY: extract
extract: ../hacspec_sha3.llbc
	$(AENEAS_EXE) -backend lean ../hacspec_sha3.llbc -split-files -dest proofs/aeneas/HacspecSha3 $(AENEAS_OPTIONS)

../hacspec_sha3.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg hax" $(CHARON_EXE) cargo --preset=aeneas