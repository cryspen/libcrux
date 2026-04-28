module Hacspec_ml_dsa.Commute.Chunk
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Libcrux_ml_dsa.Simd.Traits.Specs

(* Per-element commute lemmas bridging the impl-side `arithmetic::*` free-fn
   posts (in their existing spec form) to the trait-side per-lane post
   predicates in `Libcrux_ml_dsa.Simd.Traits.Specs`.  Each lemma converts
   one shape to the other for one i32 lane; the per-array forall is closed
   at the call site via `Classical.forall_intro`. *)

module P = Hacspec_ml_dsa.Parameters
module A = Hacspec_ml_dsa.Arithmetic
module L = FStar.Math.Lemmas
module TS = Libcrux_ml_dsa.Simd.Traits.Specs

(* Bridge: given the centered Barrett bound on `result` and the raw mod-q
   congruence between `input` and `result`, conclude `reduce_lane_post`.
   The free-fn `arithmetic::reduce` proves both conjuncts; the impl method
   reveals `Spec.MLDSA.Math.mod_q` opacity at the call site to convert
   the existing free-fn post into the raw-mod shape this lemma consumes. *)
let lemma_reduce_lane_commute (input result: i32)
    : Lemma
        (requires
          Spec.Utils.is_i32b 8380416 result /\
          (v input) % 8380417 == (v result) % 8380417)
        (ensures TS.reduce_lane_post input result)
  = reveal_opaque (`%TS.reduce_lane_post) (TS.reduce_lane_post input result)

(* Bridge: the AVX2 free fn `arithmetic::reduce` advertises its post in the
   raw `Spec.MLDSA.Math.barrett_red` shape.  This lemma converts that shape
   into the (centered Barrett bound) + (raw mod-q congruence) shape that
   `lemma_reduce_lane_commute` consumes.

   Spec.MLDSA.Math.barrett_red x = x - q * 8380417  where
     q = (x + 2^22) >> 23
   (centered Barrett reduction by 2^23).  For |x| < 2^31 - 2^22, the
   output fits in i32 with |r| < 8380417, and r ≡ x (mod 8380417). *)
#push-options "--z3rlimit 200"
let lemma_barrett_red_bound_and_mod_q (x: i32)
    : Lemma
        (requires Spec.Utils.is_i32b 2143289343 x)
        (ensures
          Spec.Utils.is_i32b 8380416 (Spec.MLDSA.Math.barrett_red x) /\
          (v (Spec.MLDSA.Math.barrett_red x)) % 8380417 == (v x) % 8380417)
  = reveal_opaque (`%Spec.MLDSA.Math.barrett_red) (Spec.MLDSA.Math.barrett_red x);
    Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    let two_22 = shift_left (mk_i32 1) (mk_i32 22) in
    assert (v two_22 == pow2 22);
    let sum = add_mod x two_22 in
    assert (v sum == v x + pow2 22);
    let q = shift_right sum (mk_i32 23) in
    assert (v q == (v x + pow2 22) / pow2 23);
    let prod = mul_mod q Spec.MLDSA.Math.v_FIELD_MODULUS in
    assert (v prod == v q * 8380417);
    let r = sub_mod x prod in
    assert (v r == v x - v q * 8380417);
    L.lemma_mod_sub (v x) 8380417 (v q)
#pop-options

(* Bridge: convert the AVX2 `arithmetic::add` post (per-lane
   `to_i32x8 lhs_future i == add_mod_opaque lhs[i] rhs[i]`) into the
   integer-equality shape consumed by `Libcrux_ml_dsa.Simd.Traits.Specs.add_post`.
   The trait pre `add_pre` (per-lane sum is i32) makes `add_mod` non-wrapping.
   `int_is_i32` from `Libcrux_ml_dsa.Simd.Traits.Specs` reduces (since
   `Hax_lib.Int.t_Int` is `int` unfolded) to the bound `-2^31 <= x <= 2^31 - 1`
   which is exactly `range x i32_inttype`. *)
let lemma_add_lane_commute (lhs rhs lhs_future: i32)
    : Lemma
        (requires
          Libcrux_ml_dsa.Simd.Traits.Specs.int_is_i32 (v lhs + v rhs) /\
          lhs_future == Spec.Intrinsics.add_mod_opaque lhs rhs)
        (ensures v lhs_future == v lhs + v rhs)
  = Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype

(* Bridge: same, for `arithmetic::subtract` / `sub_mod_opaque`. *)
let lemma_sub_lane_commute (lhs rhs lhs_future: i32)
    : Lemma
        (requires
          Libcrux_ml_dsa.Simd.Traits.Specs.int_is_i32 (v lhs - v rhs) /\
          lhs_future == Spec.Intrinsics.sub_mod_opaque lhs rhs)
        (ensures v lhs_future == v lhs - v rhs)
  = Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype

(* Bridge: convert the Tier-1 `Spec.MLDSA.Math.power2round` int-pair shape
   into `power2round_lane_post`.  Both impls' `arithmetic::power2round`
   posts state, per-lane:
     let (t0_s, t1_s) = Spec.MLDSA.Math.power2round (v input)
     v future_t0 == t0_s /\ v future_t1 == t1_s
   The trait-side post `power2round_lane_post` cites
   `Hacspec_ml_dsa.Arithmetic.power2round` (returning (r1, r0) i32 pair).
   For input in [0, q), the two specs compute the same i32 values; this
   lemma just unfolds both and lets Z3 match them. *)
#push-options "--z3rlimit 200"
let lemma_power2round_lane_commute (input future_t1 future_t0: i32)
    : Lemma
        (requires
          (let pair = Spec.MLDSA.Math.power2round (v input) in
           v future_t0 == fst pair /\ v future_t1 == snd pair))
        (ensures TS.power2round_lane_post input future_t1 future_t0)
  = reveal_opaque (`%TS.power2round_lane_post)
                  (TS.power2round_lane_post input future_t1 future_t0)
#pop-options

(* Math lemma: for any i32 input, the t1 component of
   `Spec.MLDSA.Math.power2round` lies in `[0, pow2 10)`.  The trait
   post advertises this as an unconditional per-lane bound on
   `t1_future` (cherry-pick a331580ec); the underlying arithmetic
   free-fn only states `v t1 == snd (...power2round (v input))`, so
   the bound has to come from the math spec.

   Reasoning:
     representative = (v input) % q  ∈ [0, q-1] = [0, 8380416]
     m              = representative % (pow2 13)  ∈ [0, pow2 13)
     t0             = if m > pow2 12 then m - pow2 13 else m
                       ∈ (-pow2 12, pow2 12]
     t1             = (representative - t0) / pow2 13

   - If m ≤ pow2 12: t0 = m, so representative - t0 = (representative
     / pow2 13) * pow2 13 (since m = representative % pow2 13).  Hence
     t1 = representative / pow2 13.  Since representative < q,
     t1 < q / pow2 13 = 1023 + 1/pow2 13, and as int floor:
     t1 ≤ (q-1) / pow2 13 = 1023.  So t1 ∈ [0, 1024) = [0, pow2 10).
   - If m > pow2 12: t0 = m - pow2 13, so representative - t0 =
     representative - m + pow2 13.  Since representative - m is a
     non-negative multiple of pow2 13, t1 = (representative / pow2 13) + 1.
     Worst case t1 = 1024 would require representative / pow2 13 = 1023
     and m > pow2 12.  But (q-1) / pow2 13 = 1023 only when
     representative ≥ 1023 * pow2 13 = 8380416 = q-1, and at exactly
     that value m = 0 (since (q-1) is divisible by pow2 13), which
     contradicts m > pow2 12.  So t1 ≤ 1023 in this branch too. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let lemma_power2round_t1_bound (input: i32)
    : Lemma
        (let (_, t1_s) = Spec.MLDSA.Math.power2round (v input) in
         0 <= t1_s /\ t1_s < pow2 10)
  = let q : pos = 8380417 in
    let p : pos = pow2 13 in
    assert (p == 8192);
    assert (pow2 12 == 4096);
    assert (pow2 10 == 1024);
    let representative = (v input) % q in
    L.lemma_mod_lt (v input) q;
    L.lemma_mod_plus_distr_l (v input) 0 q;
    assert (0 <= representative /\ representative <= q - 1);
    let m = representative % p in
    L.lemma_mod_lt representative p;
    L.lemma_mod_plus_distr_l representative 0 p;
    assert (0 <= m /\ m < p);
    let t0 = if m > pow2 12 then m - p else m in
    let t1 = (representative - t0) / p in
    if m > pow2 12 then begin
      assert (t0 == m - p);
      assert (representative - t0 == representative - m + p);
      L.lemma_div_mod representative p;
      assert (representative - m == (representative / p) * p);
      assert (representative - t0 == (representative / p + 1) * p);
      L.cancel_mul_div (representative / p + 1) p;
      assert (t1 == representative / p + 1);
      // representative / p ≤ (q-1) / p = 1023, but if it equals 1023
      // then representative ≥ 1023 * p = q - 1 and (q-1) % p = 0,
      // contradicting m > pow2 12.
      L.lemma_div_le representative (q - 1) p;
      assert (representative / p <= (q - 1) / p);
      assert ((q - 1) / p == 1023);
      assert (representative / p <= 1023);
      // Exclude representative/p = 1023 case under m > pow2 12.
      if representative / p = 1023 then begin
        L.lemma_div_mod representative p;
        assert (representative == 1023 * p + m);
        assert (representative <= q - 1);
        assert (1023 * p + m <= q - 1);
        // q - 1 = 1023 * p, so 1023 * p + m <= 1023 * p, thus m <= 0,
        // contradicting m > pow2 12 > 0.
        assert (1023 * p == q - 1);
        assert (m <= 0);
        ()
      end
      else assert (representative / p <= 1022);
      assert (t1 <= 1023)
    end
    else begin
      assert (t0 == m);
      assert (representative - t0 == representative - m);
      L.lemma_div_mod representative p;
      assert (representative - m == (representative / p) * p);
      L.cancel_mul_div (representative / p) p;
      assert (t1 == representative / p);
      L.lemma_div_le representative (q - 1) p;
      assert ((q - 1) / p == 1023);
      assert (t1 <= 1023)
    end
#pop-options

(* Bridge: convert the AVX2 free fn post `barrett_red(shift_left_opaque
   input 13)` into the relaxed
   `shift_left_then_reduce_lane_post` (centered-Barrett bound + mod-q
   congruence with input * 8192).  The hypothesis `0 <= v input <= 261631`
   bounds `input <<! 13 < 2^31 - 2^22` so `lemma_barrett_red_bound_and_mod_q`
   applies and produces both halves of the post. *)
#push-options "--z3rlimit 200"
let lemma_shift_left_then_reduce_lane_commute (input future: i32)
    : Lemma
        (requires
          v input >= 0 /\ v input <= 261631 /\
          future == Spec.MLDSA.Math.barrett_red
                      (Spec.Intrinsics.shift_left_opaque input (mk_i32 13)))
        (ensures TS.shift_left_then_reduce_lane_post input future)
  = Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    let shifted = Spec.Intrinsics.shift_left_opaque input (mk_i32 13) in
    assert (v shifted == v input * 8192);
    lemma_barrett_red_bound_and_mod_q shifted;
    reveal_opaque (`%TS.shift_left_then_reduce_lane_post)
                  (TS.shift_left_then_reduce_lane_post input future)
#pop-options

(* Bridge for the Portable side: the Portable `arithmetic::shift_left_then_reduce`
   post advertises mod_q congruence with `input <<! 13` plus the
   centered-Barrett bound.  This lemma converts that shape into the
   relaxed lane post. *)
let lemma_shift_left_then_reduce_lane_commute_mod_q
    (input future: i32)
    : Lemma
        (requires
          v input >= 0 /\ v input <= 261631 /\
          Spec.Utils.is_i32b 8380416 future /\
          Spec.MLDSA.Math.mod_q (v future) ==
            Spec.MLDSA.Math.mod_q (v (input <<! mk_i32 13 <: i32)))
        (ensures TS.shift_left_then_reduce_lane_post input future)
  = reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
    assert (v (input <<! mk_i32 13 <: i32) == v input * 8192);
    reveal_opaque (`%TS.shift_left_then_reduce_lane_post)
                  (TS.shift_left_then_reduce_lane_post input future)
