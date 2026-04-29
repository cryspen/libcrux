SLOW_MODULES += Libcrux_ml_kem.Vector.Rej_sample_table.fsti
SLOW_MODULES += Libcrux_ml_kem.Matrix.fst
SLOW_MODULES += Libcrux_ml_kem.Vector.Portable.Serialize.fst

ADMIT_MODULES = Libcrux_ml_kem.Ind_cca.Unpacked.fst \
	      Libcrux_ml_kem.Ind_cpa.fst \
              Libcrux_ml_kem.Vector.Neon.Arithmetic.fst \
              Libcrux_ml_kem.Vector.Neon.Compress.fst \
              Libcrux_ml_kem.Vector.Neon.fsti \
              Libcrux_ml_kem.Vector.Neon.fst \
              Libcrux_ml_kem.Vector.Neon.Ntt.fst \
              Libcrux_ml_kem.Vector.Neon.Serialize.fst \
              Libcrux_ml_kem.Vector.Neon.Vector_type.fst

# =====================================================================
# WAVE-B local-only: admit OTHER waves' modules (lane isolation, NOT
# new admits — these are owned by Wave-A or Wave-C in their own
# worktrees).  This Makefile is intentionally NOT pushed to upstream
# `trait-opacify`; it lives only in `~/libcrux-ml-kem-above-trait/`.
# Established 2026-04-29 per `proofs/agent-status/wave-B-prompt.md`
# §"WAVE-B ADMIT MAP".
# =====================================================================

# Below-trait surface (Wave-A's worktree owns these).  Wave-A closed B6
# at `2f96abe99`; remaining B-lanes (B1/B2/B3/B5) are deferred to USER-N.
ADMIT_MODULES += Libcrux_ml_kem.Vector.Portable.fst \
                 Libcrux_ml_kem.Vector.Portable.Arithmetic.fst \
                 Libcrux_ml_kem.Vector.Portable.Compress.fst \
                 Libcrux_ml_kem.Vector.Portable.Ntt.fst \
                 Libcrux_ml_kem.Vector.Portable.Sampling.fst \
                 Libcrux_ml_kem.Vector.Portable.Vector_type.fst \
                 Libcrux_ml_kem.Vector.Avx2.fst \
                 Libcrux_ml_kem.Vector.Avx2.Arithmetic.fst \
                 Libcrux_ml_kem.Vector.Avx2.Compress.fst \
                 Libcrux_ml_kem.Vector.Avx2.Ntt.fst \
                 Libcrux_ml_kem.Vector.Avx2.Sampling.fst \
                 Libcrux_ml_kem.Vector.Avx2.Serialize.fst
# ^ Invert_ntt.fst UNADMITTED 2026-04-29 by lane A5 (A5 owns this module).
# Wave-B baseline TEMP-admitted it due to hint-replay regression on
# `inv_ntt_layer_int_vec_step_reduce` Q101.  A5 plan: bump rlimit on
# step_reduce to 400 (cheap fix), then proceed to Step 3.3 / 4 / 5.

# Wave-C surface (consumer chain; Wave-C will UNADMIT post-A6/7/8).
# These admits stay through all of Wave-B; Wave-C inherits this same
# worktree.  Note: Matrix.fst and Vector.Portable.Serialize.fst are
# already admitted via SLOW_MODULES (default VERIFY_SLOW_MODULES=no).
ADMIT_MODULES += Libcrux_ml_kem.Ind_cpa.Unpacked.fst \
                 Libcrux_ml_kem.Ind_cca.fst \
                 Libcrux_ml_kem.Ind_cca.Multiplexing.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Avx2.Unpacked.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Neon.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Neon.Unpacked.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Portable.fst \
                 Libcrux_ml_kem.Ind_cca.Instantiations.Portable.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem512.fst \
                 Libcrux_ml_kem.Mlkem512.Avx2.fst \
                 Libcrux_ml_kem.Mlkem512.Avx2.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem512.Neon.fst \
                 Libcrux_ml_kem.Mlkem512.Neon.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem512.Portable.fst \
                 Libcrux_ml_kem.Mlkem512.Portable.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem512.Rand.fst \
                 Libcrux_ml_kem.Mlkem768.fst \
                 Libcrux_ml_kem.Mlkem768.Avx2.fst \
                 Libcrux_ml_kem.Mlkem768.Avx2.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem768.Neon.fst \
                 Libcrux_ml_kem.Mlkem768.Neon.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem768.Portable.fst \
                 Libcrux_ml_kem.Mlkem768.Portable.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem768.Rand.fst \
                 Libcrux_ml_kem.Mlkem1024.fst \
                 Libcrux_ml_kem.Mlkem1024.Avx2.fst \
                 Libcrux_ml_kem.Mlkem1024.Avx2.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem1024.Neon.fst \
                 Libcrux_ml_kem.Mlkem1024.Neon.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem1024.Portable.fst \
                 Libcrux_ml_kem.Mlkem1024.Portable.Unpacked.fst \
                 Libcrux_ml_kem.Mlkem1024.Rand.fst

# =====================================================================
# Trait-boundary admits — TEMPORARY, scope = trait_post-strengthening work
# =====================================================================
# These three modules sit ABOVE `vector/traits.rs` in the dep graph.  Their
# proof failures all share the same shape: subtyping checks on a loop
# accumulator's forall-in-refinement get re-proven from scratch each
# iteration, exhausting Z3's rlimit.  This is downstream fallout from the
# trait post strengthening — call sites here haven't been retuned yet.
# Confirmed failing on macOS reference run too, so admitting hides no
# regression.
#
# **REMOVE ALL THREE as soon as the trait-boundary work is done.**  They are
# tracked in `MLKEM_STATUS.md` "Trait-boundary admits" section.  Drop the
# admit in the same commit as the fix so reviewers can re-verify the bound.

# `compress_then_serialize_message` Q2 cancels at rlimit 80 (full 80 in
#   ~18 s on Mac, ~26 s here).  Assert at line 57 about Vector.Traits.fst:587.
# Phase 5: dual-trigger SMTPat `lemma_bounded_i16_array_lookup` in traits::spec
# auto-unfolds the predicate per-index (consume direction).  Intro direction
# (proving `bounded_i16_array` from per-lane bounds) handled by explicit
# `reveal_opaque` at the few call sites that need it.
# ADMIT_MODULES += Libcrux_ml_kem.Serialize.fst

# `Polynomial.ntt_multiply` Q54 cancels at rlimit 300 (full 300 in ~90 s on
#   Mac).  Subtyping on the loop accumulator refinement at line 845.
# REMOVED 2026-04-27: with Phase 2 opacity (per-branch opaque
# ntt_multiply_branch_post), the loop-accumulator forall-in-refinement
# no longer floods the SMT context with FE equations.
# ADMIT_MODULES += Libcrux_ml_kem.Polynomial.fst

# `invert_ntt_at_layer_2_` Q2 "unknown" at rlimit 400 (full 400 in ~86 s).
#   Subtyping on the loop accumulator refinement at line 149 — same forall-
#   in-refinement pattern as Polynomial above.
# REMOVED 2026-04-27: Phase 2 opacity (per-branch opaque
# inv_ntt_layer_2_step_branch_post) eliminates the SMT context flooding.
# ADMIT_MODULES += Libcrux_ml_kem.Invert_ntt.fst

FSTAR_INCLUDE_DIRS_EXTRA += ../spec \
	      $(shell git rev-parse --show-toplevel)/fstar-helpers/fstar-bitvec \
	      $(shell git rev-parse --show-toplevel)/libcrux-intrinsics/proofs/fstar/extraction \
	      $(shell git rev-parse --show-toplevel)/specs/ml-kem/proofs/fstar/commute

ENABLE_HINTS = --use_hints --record_hints

include $(shell git rev-parse --show-toplevel)/fstar-helpers/Makefile.base
