SLOW_MODULES +=

# ML-DSA verification scope (post-merge of `ml-dsa-above-trait` into
# `ml-dsa-proofs`).  This Makefile lists modules that are ADMITTED
# (default-allowlist), mirroring `libcrux-ml-kem`.  Every other .fst
# in this directory is verified by full SMT.  Every newly-extracted
# file therefore enters the verified set automatically — drop a line
# below to admit it explicitly when you cannot prove it yet, and
# delete the line as soon as it verifies.
#
# Goal: drive this list to zero.

# =====================================================================
# User-facing per-parameter-set API wrappers (12)
# =====================================================================
# Public entry points (`generate_key_pair`, `sign`, `verify`).  They
# thread through the verified core via `Ml_dsa_generic.*` (which IS
# verified).  Closing them requires top-level functional-correctness
# specs that don't exist yet.  Stretch goal for a future sprint.
ADMIT_MODULES = \
	Libcrux_ml_dsa.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_44_.Avx2.fst \
	Libcrux_ml_dsa.Ml_dsa_44_.Neon.fst \
	Libcrux_ml_dsa.Ml_dsa_44_.Portable.fst \
	Libcrux_ml_dsa.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_65_.Avx2.fst \
	Libcrux_ml_dsa.Ml_dsa_65_.Neon.fst \
	Libcrux_ml_dsa.Ml_dsa_65_.Portable.fst \
	Libcrux_ml_dsa.Ml_dsa_87_.fst \
	Libcrux_ml_dsa.Ml_dsa_87_.Avx2.fst \
	Libcrux_ml_dsa.Ml_dsa_87_.Neon.fst \
	Libcrux_ml_dsa.Ml_dsa_87_.Portable.fst

# =====================================================================
# X4-parallel matrix sampling dispatchers (4)
# =====================================================================
# Requires trait-method panic-freedom on the underlying X4 Xof hash
# functions.  Tracked as Session D in `proofs/post-merge-handoff.md`.
ADMIT_MODULES += \
	Libcrux_ml_dsa.Samplex4.fst \
	Libcrux_ml_dsa.Samplex4.Avx2.fst \
	Libcrux_ml_dsa.Samplex4.Neon.fst \
	Libcrux_ml_dsa.Samplex4.Portable.fst

# =====================================================================
# AVX2 rejection sample shuffle table + samplers (3)
# =====================================================================
# Shuffle_table is pure data computation; samplers are admit-only
# pending bit-vec body proofs (similar shape to Step 13 Track A AVX2
# closures).  Tracked as Session C in `proofs/post-merge-handoff.md`.
ADMIT_MODULES += \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.fst \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus.fst \
	Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table.fst

# =====================================================================
# Spec dispatcher (1)
# =====================================================================
# Internal spec helper; admit-only.  `rejection_sample_*_post`
# references `Spec.MLDSA.Math.rejection_sample_field_modulus` which
# carries a randomness-length precondition not yet bridged here.
ADMIT_MODULES += \
	Libcrux_ml_dsa.Specs.Simd.Portable.Sample.fst

FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell git rev-parse --show-toplevel)/specs/ml-dsa/proofs/fstar/commute

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
