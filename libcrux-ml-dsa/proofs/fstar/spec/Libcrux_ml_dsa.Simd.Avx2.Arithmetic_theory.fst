module Libcrux_ml_dsa.Simd.Avx2.Arithmetic_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Spec.Intrinsics
open Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec

(* ============================================================================
   Hand-written companion for `src/simd/avx2/arithmetic.rs` (annotation-
   uniformity sweep Batch 2).  Relocated from the `compute_hint` and `use_hint`
   fstar::before blocks.  This module is NOT generated -- edit it directly.
   ========================================================================== *)

(* --- was on `compute_hint`: proof helpers for its per-lane functional post.
   `lemma_or_and_mask_bit` closes the `(mask_a |. mask_c) &. 1` truth table for
   mask values (ones/zero) via the logor/logand value lemmas;
   `lemma_and_one_binary` gives `x &. 1 ∈ {0,1}` for any x. --- *)
let lemma_ones_zero_v (_: unit)
    : Lemma (v (ones #i32_inttype) == - 1 /\ v (zero #i32_inttype) == 0) =
  lognot_lemma_forall #i32_inttype

let lemma_and_one_binary (x: i32)
    : Lemma (v (x &. mk_i32 1) == 0 \/ v (x &. mk_i32 1) == 1) =
  logand_mask_lemma x 1

let lemma_or_and_mask_bit (a c: i32)
    : Lemma
      (requires (a == zero \/ a == ones) /\ (c == zero \/ c == ones))
      (ensures v ((a |. c <: i32) &. mk_i32 1) == (if (a = ones) || (c = ones) then 1 else 0)) =
  logor_lemma a c;
  logand_lemma (mk_i32 1) (mk_i32 1);
  lemma_ones_zero_v ()

(* For a lane that is all-ones/all-zero on both operands, the movemask sign bit
   `(a|.c) <. 0` and the low bit `(a|.c) &. 1` agree (both == a=ones||c=ones).
   This is the per-lane link between the AVX2 popcount (which counts sign bits)
   and the returned hint (which is the low bit). *)
let lemma_or_sign_and (a c: i32)
    : Lemma
      (requires (a == zero \/ a == ones) /\ (c == zero \/ c == ones))
      (ensures
        (if (a |. c <: i32) <. mk_i32 0 then 1 else 0) ==
        v (cast ((a |. c <: i32) &. mk_i32 1) <: usize)) =
  logor_lemma a c;
  logand_lemma (mk_i32 1) (mk_i32 1);
  lemma_ones_zero_v ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
(* Unfold Spec.MLDSA.Math.compute_hint (a repeati over 8 lanes) into the
   explicit 8-term lane sum, so the AVX2 popcount count-post (an 8-lane sum)
   can be bridged to compute_hint at the trait wrapper. *)
let lemma_compute_hint_8 (arr: t_Array i32 (mk_usize 8))
    : Lemma
      (ensures
        Spec.MLDSA.Math.compute_hint arr ==
        v (cast (arr.[ mk_usize 0 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 1 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 2 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 3 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 4 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 5 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 6 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 7 ] <: i32) <: usize)) =
  Spec.Utils.eq_repeati0 (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0;
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 0);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 1);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 2);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 3);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 4);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 5);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 6);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 7)
#pop-options

(* --- was on `use_hint`: clean-context helper lemmas for its functional proof:
   the pure-int matching of the AVX2 clamp/and chain to use_one_hint's
   (r1 +/- 1) % m form, and the bridge from use_one_hint to decompose_spec's
   outputs (via the admitted decompose bit-trick lemma).  Kept out of the
   leaf's SIMD context so the small-modulus reasoning does not saturate. --- *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_use_hint_value (gamma2: i32) (r0i r1i h: int)
    : Lemma
      (requires
        (v gamma2 == 95232 \/ v gamma2 == 261888) /\
        (h == 0 \/ h == 1) /\
        0 <= r1i /\
        (v gamma2 == 95232 ==> r1i < 44) /\
        (v gamma2 == 261888 ==> r1i < 16))
      (ensures
        (let m = 4190208 / (v gamma2) in
          let rph = (if r0i <= 0 then r1i - h else r1i + h) in
          let uoh = (if h = 0 then r1i else if r0i > 0 then (r1i + 1) % m else (r1i - 1) % m) in
          (v gamma2 == 95232 ==>
            (if (if rph < 0 then 43 else rph) > 43 then 0 else (if rph < 0 then 43 else rph)) == uoh) /\
          (v gamma2 == 261888 ==> rph % 16 == uoh))) =
  let m = 4190208 / (v gamma2) in
  if h = 0 then ()
  else if r0i > 0 then begin
    if r1i + 1 < m then FStar.Math.Lemmas.small_mod (r1i + 1) m
    else FStar.Math.Lemmas.cancel_mul_mod 1 m
  end
  else begin
    if r1i - 1 >= 0 then FStar.Math.Lemmas.small_mod (r1i - 1) m
    else begin
      FStar.Math.Lemmas.lemma_mod_plus (r1i - 1) 1 m;
      FStar.Math.Lemmas.small_mod (r1i - 1 + m) m
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_use_one_hint_via_spec (gamma2 r h: i32)
    : Lemma
      (requires
        (v gamma2 == 95232 \/ v gamma2 == 261888) /\
        Spec.Utils.is_i32b 8380416 r /\
        (v h == 0 \/ v h == 1))
      (ensures
        (let r0_s, r1_s = Spec.MLDSA.Math.decompose_spec gamma2 r in
          let m = 4190208 / (v gamma2) in
          Spec.MLDSA.Math.use_one_hint (v gamma2) (v r) (v h) ==
          (if v h = 0 then v r1_s
           else if v r0_s > 0 then (v r1_s + 1) % m
           else (v r1_s - 1) % m))) =
  Hacspec_ml_dsa.Commute.Chunk.lemma_decompose_spec_eq_decompose gamma2 r;
  Hacspec_ml_dsa.Commute.Chunk.lemma_decompose_bound gamma2 r
#pop-options
