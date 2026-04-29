SLOW_MODULES +=
# ML-DSA verification scope (post-merge of `ml-dsa-above-trait` into
# `ml-dsa-proofs`).  This Makefile lists modules that are verified
# (CHECK), not those that are admitted.  The two lanes formerly split
# the work at the `Libcrux_ml_dsa.Simd.Traits.{fsti,fst}` +
# `…Specs.fst` contract — below-trait verified `Simd.{Portable,Avx2}.*`,
# above-trait verified `Arithmetic`, `Polynomial`, `Matrix`, `Sample`,
# `Encoding.*`, `Ml_dsa_generic.*`, `Hash_functions.*`, `Pre_hash`,
# top-level `Ntt`.  After the merge the union of both lanes' CHECK
# scopes is verified together.
VERIFIED_MODULES = \
	Libcrux_ml_dsa.Simd.Portable.Vector_type.fst \
	Libcrux_ml_dsa.Simd.Portable.Sample.fst \
	Libcrux_ml_dsa.Simd.Portable.Arithmetic.fst \
	Libcrux_ml_dsa.Simd.Portable.Ntt.fst \
	Libcrux_ml_dsa.Simd.Portable.Invntt.fst \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Error.fst \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.fst \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.fst \
	Libcrux_ml_dsa.Simd.Portable.Encoding.T0.fst \
	Libcrux_ml_dsa.Simd.Portable.Encoding.T1.fst \
	Libcrux_ml_dsa.Simd.Portable.fst \
	Libcrux_ml_dsa.Simd.Avx2.Vector_type.fst \
	Libcrux_ml_dsa.Simd.Avx2.Arithmetic.fst \
	Libcrux_ml_dsa.Simd.Avx2.Ntt.fst \
	Libcrux_ml_dsa.Simd.Avx2.Invntt.fst \
	Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.fst \
	Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.fst \
	Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.fst \
	Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.fst \
	Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.fst \
	Libcrux_ml_dsa.Simd.Avx2.fst \
	Libcrux_ml_dsa.Simd.Traits.fsti \
	Libcrux_ml_dsa.Simd.Traits.Specs.fst \
	Libcrux_ml_dsa.Simd.Traits.fst \
	Libcrux_ml_dsa.Constants.fst \
	Libcrux_ml_dsa.Types.fst \
	Libcrux_ml_dsa.Arithmetic.fst \
	Libcrux_ml_dsa.Polynomial.fst \
	Libcrux_ml_dsa.Polynomial.Spec.fst \
	Libcrux_ml_dsa.Ntt.fst \
	Libcrux_ml_dsa.Encoding.T1.fst \
	Libcrux_ml_dsa.Encoding.Commitment.fst \
	Libcrux_ml_dsa.Encoding.Error.fst \
	Libcrux_ml_dsa.Encoding.Gamma1.fst \
	Libcrux_ml_dsa.Pre_hash.fst \
	Libcrux_ml_dsa.Encoding.T0.fst \
	Libcrux_ml_dsa.Encoding.Verification_key.fst \
	Libcrux_ml_dsa.Encoding.Signing_key.fst \
	Libcrux_ml_dsa.Encoding.Signature.fst \
	Libcrux_ml_dsa.Matrix.fst \
	Libcrux_ml_dsa.Sample.fst \
	Libcrux_ml_dsa.Hash_functions.Shake128.fst \
	Libcrux_ml_dsa.Hash_functions.Shake256.fst \
	Libcrux_ml_dsa.Hash_functions.Portable.fst \
	Libcrux_ml_dsa.Hash_functions.Simd256.fst \
	Libcrux_ml_dsa.Hash_functions.Neon.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_87_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Multiplexing.Ml_dsa_87_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Portable.Ml_dsa_87_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Avx2.Ml_dsa_87_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_44_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_65_.fst \
	Libcrux_ml_dsa.Ml_dsa_generic.Instantiations.Neon.Ml_dsa_87_.fst \
	end_of_verified_modules

VERIFIED_OR_SLOW_MODULES = $(sort $(SLOW_MODULES) $(VERIFIED_MODULES))
ADMIT_MODULES = $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fst)) $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fsti))
FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell git rev-parse --show-toplevel)/specs/ml-dsa/proofs/fstar/commute

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
