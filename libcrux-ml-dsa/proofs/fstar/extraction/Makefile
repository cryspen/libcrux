SLOW_MODULES +=
# Below-trait verification lane (branch ml-dsa-proofs).
# This lane verifies the trait contract + all impl modules.  Modules
# *above* `Libcrux_ml_dsa.Simd.Traits` (Arithmetic, Polynomial, Matrix,
# Sample, Encoding.*, Ml_dsa_generic.*, Ntt top-level, etc.) are
# deliberately left in ADMIT mode here — the dual above-trait agent's
# branch verifies them against the SAME trait pre/post defined in
# `Libcrux_ml_dsa.Simd.Traits.{fsti,fst}` and
# `Libcrux_ml_dsa.Simd.Traits.Specs`.  The two lanes meet at the trait
# contract.
VERIFIED_MODULES = \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.fst \
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
