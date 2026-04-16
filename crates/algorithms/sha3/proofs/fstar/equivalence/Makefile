FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell pwd)/../extraction

ROOTS = \
	Proof_Utils.Lemmas.fst \
	Proof_Utils.NatFold.fst \
	Impl_Spec_Keccakf.ChiFold.fst \
	Impl_Spec_Keccakf.SpecRounds.fst \
	Impl_Spec_Keccakf.fst \
	Impl_Spec_Keccakf.Generic.fst \
	Impl_Spec_Keccakf.Portable.fst \
	Impl_Spec_Keccakf.Arm64.fst \
	Impl_Spec_Sponge.Core.fst \
	Impl_Spec_Sponge.Absorb.fst \
	Impl_Spec_Sponge.Squeeze.fst \
	Impl_Spec_Sponge.Keccak.fst

# Disable context_pruning for proof modules — it strips definitions
# the normalizer needs for assert_norm and fold_range reduction.
FSTAR_EXT_FLAGS = --ext context_pruning

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
