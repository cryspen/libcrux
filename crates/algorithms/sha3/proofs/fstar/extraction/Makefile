FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction

ROOTS = \
	Impl_Spec_Keccakf.fst \
	Impl_Spec_Sponge.Core.fst \
	Impl_Spec_Sponge.Absorb.fst \
	Impl_Spec_Sponge.Squeeze.fst \
	Impl_Spec_Sponge.Keccak.fst

# Disable context_pruning for proof modules — it strips definitions
# the normalizer needs for assert_norm and fold_range reduction.
FSTAR_EXT_FLAGS = --ext context_pruning

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
