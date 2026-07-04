//! Trusted-base proof utilities for libcrux-ml-dsa F* verification.
//!
//! Staging area for facts about MODELED PRIMITIVES that are true but not (yet)
//! provable within ml-dsa's F* dependency closure. These are `assume val`s —
//! part of the trusted base, like the intrinsic models themselves — collected
//! here (rather than duplicated at the use sites) and tagged with the place they
//! should eventually be upstreamed to and discharged.
//!
//! UPSTREAM TARGETS:
//!  * `lemma_movemask_ps_bound` -> core-models. Give the abstract
//!    `Libcrux_core_models.Core_arch.X86.Avx.e_mm256_movemask_ps'` val the
//!    refinement `r: i32{v r >= 0 /\ v r < 256}` (it is an 8-lane sign-bit mask;
//!    justified by `Int_vec.Lemmas`, where movemask == sum of `2^i` over the set
//!    lanes). It is not provable here because `Int_vec.Lemmas` (which pulls in
//!    `Tactics.Circuits`) is outside ml-dsa's F* dependency closure.
//!  * `lemma_count_ones_nibble` -> hax-lib `Rust_primitives.Arithmetic`.
//!    Strengthen `count_ones_i32`'s spec (or add a general `count_ones_lt_pow2`):
//!    `v x < pow2 n ==> v (count_ones x) <= n`. The current spec only bounds the
//!    result by `<= 32`, with no relationship to the value.
//!  * `lemma_count_ones_byte_exact` -> hax-lib `Rust_primitives.Arithmetic` (or
//!    core-models). The EXACT popcount identity for an 8-bit value, phrased over
//!    the 8 sign/set bits `b0..b7`: if `m == sum_j (b_j ? 2^j : 0)` then
//!    `count_ones m == sum_j (b_j ? 1 : 0)`. `count_ones_i32` is an uninterpreted
//!    `val` (only `<= 32` is known), so this cannot be proved within ml-dsa's F*
//!    closure. Same trusted class as the two bounds above and ml-kem's
//!    `count_ones_u8_popcount8`; validated exhaustively (0..=255) by the
//!    core-models test `track_i_axiom_transcription_tests::count_ones_popcount8_formula`
//!    in `crates/utils/core-models/src/core_arch/x86/interpretations.rs`. Consumed
//!    by the AVX2 `compute_hint` count post: `mm256_movemask_ps` returns exactly
//!    `sum_j (lane_j < 0 ? 2^j : 0)`, so `count_ones(movemask) == #{negative lanes}`.

// The lemmas are emitted as standalone F* `assume val`s into
// `Libcrux_ml_dsa.Proof_utils`; the marker below just gives hax an item to hang
// the module on (the whole module is `#[cfg(hax)]`, so it has no runtime form).
#[hax_lib::fstar::before(
    r#"
assume
val lemma_movemask_ps_bound (a: Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Lemma
      (ensures
        v (Libcrux_intrinsics.Avx2.mm256_movemask_ps a) >= 0 /\
        v (Libcrux_intrinsics.Avx2.mm256_movemask_ps a) < 256)

assume
val lemma_count_ones_nibble (x: i32)
    : Lemma (requires v x >= 0 /\ v x < 16)
      (ensures v (Core_models.Num.impl_i32__count_ones x) <= 4)

assume
val lemma_count_ones_byte (x: i32)
    : Lemma (requires v x >= 0 /\ v x < 256)
      (ensures v (Core_models.Num.impl_i32__count_ones x) <= 8)

assume
val lemma_count_ones_byte_exact (m: i32) (b0 b1 b2 b3 b4 b5 b6 b7: bool)
    : Lemma
      (requires
        v m ==
        (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
        (if b6 then 64 else 0) + (if b7 then 128 else 0))
      (ensures
        v (Core_models.Num.impl_i32__count_ones m) ==
        (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) +
        (if b3 then 1 else 0) + (if b4 then 1 else 0) + (if b5 then 1 else 0) +
        (if b6 then 1 else 0) + (if b7 then 1 else 0))
"#
)]
pub(crate) fn proof_utils_module_marker() -> bool {
    true
}
