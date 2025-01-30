SLOW_MODULES += 
ADMIT_MODULES =
FSTAR_INCLUDE_DIRS_EXTRA += $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction
OTHERFLAGS += --z3version 4.13.3
OTHERFLAGS += --ext context_pruning

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
