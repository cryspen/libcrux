SLOW_MODULES += 
ADMIT_MODULES =
FSTAR_INCLUDE_DIRS_EXTRA += $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
