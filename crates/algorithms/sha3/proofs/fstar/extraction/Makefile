FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

# No explicit ROOTS — default picks up all .fst/.fsti in this directory.
# These are hax-generated modules; they typecheck but carry no proof obligations.

FSTAR_EXT_FLAGS = --ext context_pruning

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
