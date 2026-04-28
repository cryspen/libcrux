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
