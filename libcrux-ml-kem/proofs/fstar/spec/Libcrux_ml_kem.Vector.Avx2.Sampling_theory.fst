module Libcrux_ml_kem.Vector.Avx2.Sampling_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

(* Hand-written proof theory relocated from src/vector/avx2/sampling.rs
   `hax_lib::fstar::before` blocks (byte-exact raw-string contents, verified verbatim
   against the green extracted module). Consumed only by that module. *)

(* Trusted axiom (Track I, 2026-06-10): semantics of the dynamic-mask byte
   shuffle. `BitVec.Intrinsics.mm_shuffle_epi8`'s tactic routes masks that are
   not `mm_set_epi8` literals (such as the `mm_loadu_si128`-loaded
   REJECTION_SAMPLE_SHUFFLE_TABLE rows below) to the uninterpreted
   `BitVec.Intrinsics.mm_shuffle_epi8_no_semantics`. This axiom gives that
   symbol the PSHUFB hardware semantics, transcribed from the executable
   core-models reference `crates/utils/core-models/src/core_arch/x86.rs`
   (`extra::mm_shuffle_epi8_u8_array`, the model behind
   `ssse3::_mm_shuffle_epi8`):

     result bit i = let nth = i / 8 in
                    let idx = byte `nth` of the mask (bits LSB-first) in
                    if idx > 127 then 0 else a ((idx % 16) * 8 + i % 8)

   Validated against core-models by the differential test
   `track_i_axiom_transcription_tests::shuffle_epi8_dynamic_mask_formula` in
   `crates/utils/core-models/src/core_arch/x86/interpretations.rs`. Kept
   ml-kem-local (not in the shared BitVec.Intrinsics.fsti) to avoid a
   stale-cascade into the sha3 / ml-dsa proof trees. *)
assume val mm_shuffle_epi8_no_semantics_lemma (a b: bit_vec 128) (i: nat{i < 128})
  : Lemma
    (BitVec.Intrinsics.mm_shuffle_epi8_no_semantics a b i ==
      (let nth = i / 8 in
       let idx: nat =
         b (8 * nth) + 2 * b (8 * nth + 1) + 4 * b (8 * nth + 2) + 8 * b (8 * nth + 3) +
         16 * b (8 * nth + 4) + 32 * b (8 * nth + 5) + 64 * b (8 * nth + 6) +
         128 * b (8 * nth + 7)
       in
       if idx > 127 then 0 else a ((idx % 16) * 8 + i % 8)))

(* Trusted axiom (Track I M2, 2026-06-10): `u8::count_ones` counts set bits.
   `Rust_primitives.Arithmetic.count_ones_u8` is an uninterpreted `val` in
   hax-lib (only `v r <= 8` is known); this axiom gives it popcount
   semantics via the bit recursion `popcount8 g = if g = 0 then 0 else
   g % 2 + popcount8 (g / 2)` (Hacspec_ml_kem.Commute.Rej_table.popcount8).
   Validated exhaustively (x in 0..=255) against the executable
   `u8::count_ones` by the core-models test
   `track_i_axiom_transcription_tests::count_ones_popcount8_formula` in
   `crates/utils/core-models/src/core_arch/x86/interpretations.rs`. *)
assume val count_ones_u8_popcount8 (x: u8)
  : Lemma (v (Rust_primitives.Arithmetic.count_ones_u8 x) ==
           Hacspec_ml_kem.Commute.Rej_table.popcount8 (v x))

(* Seal the trusted shuffle semantics into the
   Hacspec_ml_kem.Commute.Rej_table.shuffle_semantics atom in its own
   context (the raw per-bit forall must not leak into any consumer VC). *)
let lemma_shuffle_semantics_of_axiom (a mask res: bit_vec 128)
  : Lemma
    (requires res == BitVec.Intrinsics.mm_shuffle_epi8_no_semantics a mask)
    (ensures Hacspec_ml_kem.Commute.Rej_table.shuffle_semantics a mask res)
  = Classical.forall_intro (mm_shuffle_epi8_no_semantics_lemma a mask);
    Hacspec_ml_kem.Commute.Rej_table.intro_shuffle_semantics a mask res

(* Driver: every kept lane (j < popcount8 g) of a shuffled half is in
   [0, 3328].  Establishes the sealed atoms of
   Hacspec_ml_kem.Commute.Rej_table (shuffle_semantics via the axiom
   above, mask/row/half links from the term equalities) and composes the
   clean-context per-lane lemma lemma_half_lane_bounded. *)
#restart-solver
#push-options "--z3rlimit 300 --split_queries always"
let lemma_half_done
    (potential: bit_vec 256) (a mask res: bit_vec 128)
    (row: t_Array u8 (mk_usize 16)) (half: nat{half <= 1}) (g: nat{g < 256})
  : Lemma
    (requires
      res == BitVec.Intrinsics.mm_shuffle_epi8_no_semantics a mask /\
      mask == BitVec.Intrinsics.mm_loadu_si128 row /\
      row ==
      Seq.index Libcrux_ml_kem.Vector.Rej_sample_table.v_REJECTION_SAMPLE_SHUFFLE_TABLE g /\
      (half == 0 ==> a == BitVec.Intrinsics.mm256_castsi256_si128 potential) /\
      (half == 1 ==> a == BitVec.Intrinsics.mm256_extracti128_si256 (mk_i32 1) potential) /\
      Hacspec_ml_kem.Commute.Rej_table.top_bits_clear potential /\
      Hacspec_ml_kem.Commute.Rej_table.good_bits g potential half)
    (ensures
      forall (j: nat{j < 8}).
        j < Hacspec_ml_kem.Commute.Rej_table.popcount8 g ==>
        (v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) >= 0 /\
         v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) <= 3328))
  = lemma_shuffle_semantics_of_axiom a mask res;
    Hacspec_ml_kem.Commute.Rej_table.lemma_mask_of_row_loadu mask row;
    Hacspec_ml_kem.Commute.Rej_table.intro_row_of_table row g;
    Hacspec_ml_kem.Commute.Rej_table.lemma_half_of_cast a potential half;
    introduce forall (j: nat{j < 8}).
        j < Hacspec_ml_kem.Commute.Rej_table.popcount8 g ==>
        (v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) >= 0 /\
         v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) <= 3328)
    with introduce j < Hacspec_ml_kem.Commute.Rej_table.popcount8 g ==>
        (v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) >= 0 /\
         v (Seq.index (Libcrux_intrinsics.Avx2_extract.vec128_as_i16x8 res) j) <= 3328)
    with _. Hacspec_ml_kem.Commute.Rej_table.lemma_half_lane_bounded potential a mask res row half g j
#pop-options
