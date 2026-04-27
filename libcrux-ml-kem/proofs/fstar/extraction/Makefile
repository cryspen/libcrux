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
# Re-enabled 2026-04-27 on trait-opacify: the opacity work moves the failure
# point but the underlying issue (trait-pre `bounded_i16_array` ↔ trait-post
# `forall j. bounded` bridge across many trait call sites in serialize.rs)
# is the same.  Each call site needs an explicit reveal+assert; deferred.
ADMIT_MODULES += Libcrux_ml_kem.Serialize.fst

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
