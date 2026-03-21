FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/crates/algorithms/sha3/proofs/fstar/extraction \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

ADMIT_MODULES += Sha3_Equivalence.fst

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
