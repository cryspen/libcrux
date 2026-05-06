FSTAR_INCLUDE_DIRS_EXTRA += \
	$(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	$(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	../stubs \
	../extraction

# Portable keccakf1600 equivalence proofs.
# (Platform variants and sponge-level proofs ship in follow-up PRs.)
ROOTS = \
	Proof_Utils.Lemmas.fst \
	Proof_Utils.NatFold.fst \
	Proof_Utils.FoldRange.fst \
	EquivImplSpec.Keccakf.ChiFold.fst \
	EquivImplSpec.Keccakf.SpecRounds.fst \
	EquivImplSpec.Keccakf.Generic.fst \
	EquivImplSpec.Keccakf.Portable.fst

FSTAR_EXT_FLAGS = --ext context_pruning

# SMT replay hints are tracked alongside the proofs so fresh checkouts
# replay them rather than re-searching Z3 (the heavy lemma_chi_outer_unfolds_generic
# query is reproducible but slow without hints — minutes vs seconds).
HINT_DIR = $(shell pwd)/.hints
ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
