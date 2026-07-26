FSTAR_INCLUDE_DIRS_EXTRA += \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell pwd)/../stubs \
	      $(shell pwd)/../extraction

# PORTABLE-ONLY roots. The SIMD equivalence proofs (Keccakf.{Arm64,Avx2},
# Sponge.{Arm64,Avx2}.*, Correctness.{Avx2,Neon}) are DEFERRED: upstream main
# flattened simd/{arm64,avx2} into unproven impl modules, so the campaign's
# store_block proof structure they depend on needs rework first. See
# ../../verification_status.md, "Deferred SIMD store_block proofs".
ROOTS = \
	Proof_Utils.Lemmas.fst \
	Proof_Utils.NatFold.fst \
	Proof_Utils.FoldRange.fst \
	EquivImplSpec.Keccakf.ChiFold.fst \
	EquivImplSpec.Keccakf.Generic.fst \
	EquivImplSpec.Keccakf.Portable.fst \
	EquivImplSpec.Sponge.Generic.Core.fst \
	EquivImplSpec.Sponge.Generic.Squeeze.fst \
	EquivImplSpec.Sponge.Portable.fst \
	EquivImplSpec.Sponge.Portable.Steps.fst \
	Hacspec_sha3.Sponge.Lemmas.fst \
	EquivImplSpec.Sponge.Portable.SqueezeAPI.fst \
	EquivImplSpec.Correctness.Portable.fst \
	EquivImplSpec.Keccakf.SpecRounds.fst

# Same per-algorithm cache/hints isolation as ../extraction/Makefile, and the
# place the committed EquivImplSpec.*.hints actually live.
CACHE_DIR := ../cache
HINT_DIR  := ../hints

# Disable context_pruning for proof modules — it strips definitions
# the normalizer needs for assert_norm and fold_range reduction.
FSTAR_EXT_FLAGS = --ext context_pruning

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
