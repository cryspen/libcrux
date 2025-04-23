SLOW_MODULES += 
VERIFIED_MODULES = \
	Minicore.Abstractions.Bit.fst \
	Minicore.Abstractions.Bitvec.Int_vec_interp.fst \
	Minicore.Abstractions.Bitvec.fst \
	Minicore.Abstractions.Funarr.fst \
	Minicore.Core_arch.X86.Avx.fst \
	Minicore.Core_arch.X86.Avx2.fst \
	Minicore.Core_arch.X86.Extra.fst \
	Minicore.Core_arch.X86.Interpretations.Int_vec.Lift_lemmas.fst \
	Minicore.Core_arch.X86.Interpretations.Int_vec.fst \
	Minicore.Core_arch.X86.Sse2.fst \
	Minicore.Core_arch.X86.Ssse3.fst \
	Minicore.Core_arch.X86.fst

ADMIT_MODULES = $(filter-out ${VERIFIED_MODULES}, $(wildcard *.fst)) $(filter-out ${VERIFIED_MODULES}, $(wildcard *.fsti))
FSTAR_INCLUDE_DIRS_EXTRA += $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-ml-kem/proofs/fstar/spec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction
OTHERFLAGS += --z3version 4.13.3
OTHERFLAGS += --ext context_pruning

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
