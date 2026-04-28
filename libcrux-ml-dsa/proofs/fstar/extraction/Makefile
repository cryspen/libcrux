SLOW_MODULES +=
# Above-trait verification lane (branch ml-dsa-above-trait).
# All Libcrux_ml_dsa.Simd.{Portable,Avx2}.* modules are deliberately
# left in ADMIT mode here — the dual below-trait agent's branch verifies
# them against the SAME strengthened trait pre/post defined in
# Libcrux_ml_dsa.Simd.Traits.{fsti,fst} and Libcrux_ml_dsa.Simd.Traits.Specs.
# The two lanes meet at the trait contract.
VERIFIED_MODULES = \
	Libcrux_ml_dsa.Simd.Traits.fsti \
	Libcrux_ml_dsa.Simd.Traits.Specs.fst \
	Libcrux_ml_dsa.Simd.Traits.fst \
	Libcrux_ml_dsa.Constants.fst \
	Libcrux_ml_dsa.Types.fst \
	Libcrux_ml_dsa.Arithmetic.fst \
	Libcrux_ml_dsa.Polynomial.fst \
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
