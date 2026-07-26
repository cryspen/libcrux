FSTAR_INCLUDE_DIRS_EXTRA += \
	$(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	$(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	../stubs \
	../equivalence

# Default ROOTS (all .fst/.fsti here) minus the campaign's hand-written
# store-block helper modules: they are cited only by the deferred SIMD
# store_block proofs (see ../../verification_status.md, "Deferred SIMD
# store_block proofs") and are kept tracked for the rework, not built.
ROOTS = $(filter-out \
	Libcrux_sha3.Simd.Arm64.StoreBlockHelpers.fst \
	Libcrux_sha3.Simd.Avx2.StoreBlockHelpers.fst, \
	$(wildcard *.fst *.fsti))

# Deferred SIMD store_block proofs: upstream main flattened simd/{arm64,avx2}
# into single ~200-line unproven impl modules; the campaign's ~2200-line
# opaque-range store proofs were written against the old submodule structure
# and need rework before they can re-attach. Until then the flat SIMD impl
# modules are admitted (documented trust obligations, G3 module mirrors).
# trusted-module: Libcrux_sha3.Simd.Arm64 : pending-proof(sha3-simd-deferral): main flattened simd/arm64 into an unproven impl; campaign store proofs need rework
ADMIT_MODULES += Libcrux_sha3.Simd.Arm64.fst
# trusted-module: Libcrux_sha3.Simd.Avx2 : pending-proof(sha3-simd-deferral): main flattened simd/avx2 into an unproven impl; campaign store proofs need rework
ADMIT_MODULES += Libcrux_sha3.Simd.Avx2.fst
# The SIMD generic-keccak consumers keccak2/keccak4 carry Hax_lib.v_assert
# obligations (from runtime assert!s) that the campaign discharged via
# requires/ensures contracts in generic_keccak/simd{128,256}.rs, which cite
# the deferred SIMD equivalence modules. Deferred with the same obligation.
# trusted-module: Libcrux_sha3.Generic_keccak.Simd128 : pending-proof(sha3-simd-deferral): keccak2 asserts were discharged by campaign SIMD equivalence contracts; needs rework
ADMIT_MODULES += Libcrux_sha3.Generic_keccak.Simd128.fst
# trusted-module: Libcrux_sha3.Generic_keccak.Simd256 : pending-proof(sha3-simd-deferral): keccak4 asserts were discharged by campaign SIMD equivalence contracts; needs rework
ADMIT_MODULES += Libcrux_sha3.Generic_keccak.Simd256.fst

FSTAR_EXT_FLAGS = --ext context_pruning
ENABLE_HINTS = --use_hints --record_hints

# Per-algorithm F* cache + hints, isolated from other algorithms. Each
# algorithm extracts the shared dep crates (core-models/secrets/intrinsics)
# under its OWN config (e.g. ml-kem uses --cfg pre_core_models), so their
# .checked and .hints must NOT share one dir in a single working tree or
# they clobber each other. Relative to this extraction dir => <crate>/proofs/fstar/{cache,hints}.
CACHE_DIR := ../cache
HINT_DIR  := ../hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
