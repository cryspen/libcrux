SLOW_MODULES += Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.fst
VERIFIED_MODULES = \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.fsti \
	Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.fst \
	Libcrux_ml_dsa.Simd.Portable.Arithmetic.fsti \
	Libcrux_ml_dsa.Simd.Portable.Arithmetic.fst \
	Libcrux_ml_dsa.Simd.Avx2.Arithmetic.fst \
	Libcrux_ml_dsa.Simd.Traits.fsti \
	Libcrux_ml_dsa.Simd.Traits.fst \
	end_of_verified_modules
VERIFIED_OR_SLOW_MODULES = $(sort $(SLOW_MODULES) $(VERIFIED_MODULES))
ADMIT_MODULES = $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fst)) $(filter-out ${VERIFIED_OR_SLOW_MODULES}, $(wildcard *.fsti))
FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction
OTHERFLAGS += --z3version 4.13.3
OTHERFLAGS += --ext context_pruning

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
