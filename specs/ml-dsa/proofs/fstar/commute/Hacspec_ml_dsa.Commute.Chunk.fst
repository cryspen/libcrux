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

(* === F-1 restructuring (above-trait verdict 7a4dc28df, option d) ===
   The trait pre `is_i32b_array_opaque FIELD_MAX` for use_hint /
   decompose / compute_hint is intentionally weaker than the lane
   posts' `[0, q)`-conditional `==>` shape.  Each impl-side commute
   is split into two lemmas:
   (1) Unconditional bound — discharges the new cherry-picked
       array-level bound conjuncts (44 / 16 for use_hint, 95232 /
       44 / 261888 / 16 for decompose, 44 / 16 for compute_hint
       hint_future).  Proved over any input by inspection of the
       impl's internal normalize / `% m` step.
   (2) Conditional equation — uses `introduce ... with hyp.` to
       produce the lane post's `==>` shape, discharging the
       Spec-vs-Hacspec equivalence under `v input ∈ [0, q)`. *)

(* Math lemma: for `g ∈ {95232, 261888}` and any int `r`, the `r1`
   component of `Spec.MLDSA.Math.decompose g r` lies in `[0, m)` where
   m = 4190208 / g (= 44 for γ2=95232, = 16 for γ2=261888).

   Reasoning (mirrors lemma_power2round_t1_bound):
     r_q = r % q  ∈ [0, q-1] = [0, m*twog]   where twog = 2g, q-1 = m*twog
     r_g = mod_p r_q twog  ∈ (-g, g]
     - Special case r_q - r_g = q-1: spec returns r1 = 0 ∈ [0, m).
     - Otherwise: r1 = (r_q - r_g) / twog.  Two sub-cases on r_g_raw =
       r_q % twog ∈ [0, twog):
       (A) r_g_raw ≤ g: r_g = r_g_raw, r_q - r_g = (r_q / twog) * twog,
           r1 = r_q / twog ∈ [0, m].  r1 = m iff r_q = m*twog = q-1
           and r_g_raw = 0, which gives r_q - r_g = q-1 → special case
           (excluded).  So r1 ≤ m-1 in non-special.
       (B) r_g_raw > g: r_g = r_g_raw - twog, r_q - r_g = (r_q/twog + 1)*twog,
           r1 = r_q/twog + 1 ∈ [1, m+1].  r1 = m+1 would need r_q ≥
           m*twog = q-1, but then r_g_raw = (q-1) % twog = 0 ≤ g
           (case A), contradiction.  r1 = m iff r_q/twog = m-1, giving
           r_q - r_g = m*twog = q-1 → special (excluded).  So r1 ≤ m-1
           in non-special. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
let lemma_spec_decompose_r1_bound (g: int) (r: int)
    : Lemma
        (requires (g == 95232 \/ g == 261888))
        (ensures
          (let r_q = r % 8380417 in
           let r_g = Spec.Utils.mod_p r_q (g * 2) in
           let m = 4190208 / g in
           let r1 = if r_q - r_g = 8380416 then 0 else (r_q - r_g) / (g * 2) in
           0 <= r1 /\ r1 < m))
  = let q : pos = 8380417 in
    let twog : pos = g * 2 in
    let m : pos = 4190208 / g in
    assert (m * twog == 8380416);
    let r_q = r % q in
    L.lemma_mod_lt r q;
    assert (0 <= r_q /\ r_q <= q - 1);
    let r_g_raw = r_q % twog in
    L.lemma_mod_lt r_q twog;
    assert (0 <= r_g_raw /\ r_g_raw < twog);
    assert (twog / 2 == g);
    let r_g = Spec.Utils.mod_p r_q twog in
    assert (r_g == (if r_g_raw > g then r_g_raw - twog else r_g_raw));
    L.lemma_div_mod r_q twog;
    assert (r_q == (r_q / twog) * twog + r_g_raw);
    if r_q - r_g = q - 1 then ()
    else if r_g_raw > g then begin
      assert (r_g == r_g_raw - twog);
      assert (r_q - r_g == (r_q / twog) * twog + twog);
      assert (r_q - r_g == (r_q / twog + 1) * twog);
      L.cancel_mul_div (r_q / twog + 1) twog;
      assert ((r_q - r_g) / twog == r_q / twog + 1);
      // In non-special: r_q - r_g != q - 1 = m*twog, so r_q/twog + 1 != m.
      // Upper bound: r_q ≤ q-1 = m*twog, but if r_q = q-1 then r_g_raw = 0,
      // contradicting r_g_raw > g.  So r_q ≤ q-2, hence r_q/twog ≤ (q-2)/twog.
      assert ((q - 2) / twog == m - 1);
      L.lemma_div_le r_q (q - 2) twog;
      // r_q/twog ≤ m-1, so r_q/twog + 1 ≤ m.  And ≠ m (non-special), so ≤ m-1.
      ()
    end
    else begin
      assert (r_g == r_g_raw);
      assert (r_q - r_g == (r_q / twog) * twog);
      L.cancel_mul_div (r_q / twog) twog;
      assert ((r_q - r_g) / twog == r_q / twog);
      // r_q ≤ q-1 = m*twog, so r_q/twog ≤ m.  If r_q/twog = m then
      // r_q ≥ m*twog = q-1, hence r_q = q-1 and r_g_raw = (q-1) % twog = 0,
      // r_g = 0, r_q - r_g = q - 1 → special case (excluded).  So in
      // non-special r_q/twog ≤ m-1.
      L.lemma_div_le r_q (q - 1) twog;
      assert ((q - 1) / twog == m);
      ()
    end
#pop-options

(* Unconditional bound for `Spec.MLDSA.Math.use_one_hint`.  The Spec
   computes either `r1` (hint=0) or `(r1 ± 1) % (4190208 / g)`
   (hint=1).  In both cases the result lies in `[0, m)` where
   m = 4190208 / g.  hint=1 follows from `lemma_mod_lt`; hint=0
   reduces to `lemma_spec_decompose_r1_bound`. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_use_one_hint_bound (g r hint: i32)
    : Lemma
        (requires
          (v g == 95232 \/ v g == 261888) /\
          (v hint == 0 \/ v hint == 1))
        (ensures
          (let res = Spec.MLDSA.Math.use_one_hint (v g) (v r) (v hint) in
           (v g == 95232 ==> 0 <= res /\ res < 44) /\
           (v g == 261888 ==> 0 <= res /\ res < 16)))
  = let m : int = 4190208 / v g in
    assert (m == 44 \/ m == 16);
    let (r0_s, r1_s, _) = Spec.MLDSA.Math.decompose (v g) (v r) in
    lemma_spec_decompose_r1_bound (v g) (v r);
    if v hint = 0 then ()
    else if r0_s > 0 then L.lemma_mod_lt (r1_s + 1) m
    else L.lemma_mod_lt (r1_s - 1) m
#pop-options

(* Sub-lemma: `Hacspec_ml_dsa.Arithmetic.mod_pm` matches `Spec.Utils.mod_p`
   in v-image, for non-negative `a` and positive even `m` fitting in i32.
   The Hacspec version computes `((a%m)+m)%m` in i64 then folds the
   half-shift; both produce the centered representative in `(-m/2, m/2]`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_mod_pm_eq_mod_p (a m: i32)
    : Lemma
        (requires v a >= 0 /\ v a < 8380417 /\
                  v m > 0 /\ v m % 2 == 0 /\ v m <= 1000000)
        (ensures
          v (Hacspec_ml_dsa.Arithmetic.mod_pm a m) == Spec.Utils.mod_p (v a) (v m))
  = let a64 : i64 = cast a <: i64 in
    let m64 : i64 = cast m <: i64 in
    assert (v a64 == v a /\ v m64 == v m);
    let r1 = a64 %! m64 in
    L.lemma_mod_lt (v a) (v m);
    assert (v r1 == v a % v m);
    let r2 = r1 +! m64 in
    assert (v r2 == v a % v m + v m);
    let r3 = r2 %! m64 in
    L.lemma_mod_plus (v a % v m) 1 (v m);
    L.modulo_lemma (v a % v m) (v m);
    assert (v r3 == v a % v m);
    let r32 : i32 = cast r3 <: i32 in
    assert (v r32 == v a % v m);
    let half = m /! mk_i32 2 in
    assert (v half == v m / 2)
#pop-options

(* Bridge: under `v input ∈ [0, q)` and `v gamma2 ∈ {95232, 261888}`,
   the i32 `Hacspec.decompose` agrees in v-image with the int-level
   `Spec.MLDSA.Math.decompose` (note layouts differ: Spec returns
   `(r0, r1, bool)`, Hacspec returns `(r1, r0)` i32 pair). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 600"
let lemma_decompose_bridge (input gamma2: i32)
    : Lemma
        (requires
          (v gamma2 == 95232 \/ v gamma2 == 261888) /\
          v input >= 0 /\ v input < 8380417)
        (ensures
          (let (r0_s, r1_s, _) = Spec.MLDSA.Math.decompose (v gamma2) (v input) in
           let (r1_h, r0_h) = Hacspec_ml_dsa.Arithmetic.decompose input gamma2 in
           v r1_h == r1_s /\ v r0_h == r0_s))
  = let q = 8380417 in
    let twog = v gamma2 * 2 in
    // Hacspec body: r_plus = input %! Q, fixup, alpha = 2*gamma2, r0 = mod_pm,
    //               then if/else.
    let r_plus0 = input %! Hacspec_ml_dsa.Parameters.v_Q in
    L.small_mod (v input) q;
    assert (v r_plus0 == v input);
    // r_plus0 >= 0, so the fixup branch is unchanged.
    let alpha = mk_i32 2 *! gamma2 in
    assert (v alpha == twog);
    let r0_h = Hacspec_ml_dsa.Arithmetic.mod_pm r_plus0 alpha in
    lemma_mod_pm_eq_mod_p r_plus0 alpha;
    assert (v r0_h == Spec.Utils.mod_p (v input) twog);
    // Spec body: r_q = input % q, r_g = mod_p r_q twog, etc.
    L.small_mod (v input) q;
    assert ((v input) % q == v input);
    // The branch comparisons match because v r_plus0 - v r0_h fits in i32.
    let diff = r_plus0 -! r0_h in
    assert (v r0_h > -(v gamma2) /\ v r0_h <= v gamma2);
    assert (v diff == v input - v r0_h);
    ()
#pop-options

(* Conditional equation: under `v input ∈ [0, q)`, the Spec.MLDSA.Math
   and Hacspec computations of use_one_hint agree.  The lane post's
   `==>` shape is discharged via `introduce ... with hyp`.  Outside
   `[0, q)`, the lane post is vacuously true (the `==>` premise
   fails). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 600"
let lemma_use_hint_lane_commute_conditional
    (gamma2 input hint future_hint: i32)
    : Lemma
        (requires
          (v gamma2 == 95232 \/ v gamma2 == 261888) /\
          (v hint == 0 \/ v hint == 1) /\
          v future_hint == Spec.MLDSA.Math.use_one_hint (v gamma2) (v input) (v hint))
        (ensures TS.use_hint_lane_post gamma2 input hint future_hint)
  = reveal_opaque (`%TS.use_hint_lane_post)
                  (TS.use_hint_lane_post gamma2 input hint future_hint);
    introduce
        v input >= 0 /\ v input < 8380417 /\ (v hint == 0 \/ v hint == 1) ==>
        v future_hint == v (Hacspec_ml_dsa.Arithmetic.uuse_hint (v hint = 1) input gamma2)
    with hyp.
      let m_int = 4190208 / v gamma2 in
      assert (m_int == 44 \/ m_int == 16);
      let (r0_s, r1_s, _) = Spec.MLDSA.Math.decompose (v gamma2) (v input) in
      let (r1_h, r0_h) = Hacspec_ml_dsa.Arithmetic.decompose input gamma2 in
      lemma_decompose_bridge input gamma2;
      lemma_spec_decompose_r1_bound (v gamma2) (v input);
      assert (v r1_h == r1_s /\ v r0_h == r0_s);
      assert (0 <= r1_s /\ r1_s < m_int);
      // Hacspec uses `m_h = (Q-1) /! (2 *! gamma2)` which equals m_int.
      let m_h : i32 = (Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1) /! (mk_i32 2 *! gamma2) in
      assert (v m_h == m_int);
      // Note: in F*'s hax-lib, `%!` on machine ints is Euclidean (returns
      // non-negative values strictly less than the modulus), the same as
      // F*'s int `%`.  So the i32 expressions match the int expressions
      // directly under v-image, modulo i32-range checks.
      if v hint = 0 then ()
      else if r0_s > 0 then begin
        // Spec: (r1_s + 1) % m_int.  Hacspec: (r1_h +! 1) %! m_h.
        let one_plus = r1_h +! mk_i32 1 in
        assert (v one_plus == r1_s + 1)
      end
      else begin
        // Spec: (r1_s - 1) % m_int.  Hacspec: (((r1_h -! 1) %! m_h) +! m_h) %! m_h.
        let m1 = r1_h -! mk_i32 1 in
        assert (v m1 == r1_s - 1);
        let s1 = m1 %! m_h in
        L.lemma_mod_lt (v m1) m_int;
        assert (v s1 == (r1_s - 1) % m_int /\ 0 <= v s1 /\ v s1 < m_int);
        let s2 = s1 +! m_h in
        assert (v s2 == (r1_s - 1) % m_int + m_int);
        L.lemma_mod_plus ((r1_s - 1) % m_int) 1 m_int;
        L.small_mod ((r1_s - 1) % m_int) m_int;
        assert (v (s2 %! m_h) == (r1_s - 1) % m_int)
      end
#pop-options

(* === Track 2: paired-lemma template for decompose, compute_hint === *)

(* Bound lemma for decompose (paired-lemma template).  Used by the
   Portable (and AVX2) impls to discharge the array-level bound
   conjuncts on `low_future` (= Spec.r0; `is_i32b_array g`) and
   `high_future` (= Spec.r1; `is_i32b_array (4190208/g)`).

   Spec returns r0 = either `r_g` (non-special) or `r_g - 1` (special,
   when r_q - r_g = q-1, which forces r_g = 0 and r0 = -1).
   Both cases yield r0 ∈ [-g, g]. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"
let lemma_decompose_bound (gamma2 r: i32)
    : Lemma
        (requires (v gamma2 == 95232 \/ v gamma2 == 261888))
        (ensures
          (let (r0_s, r1_s, _) = Spec.MLDSA.Math.decompose (v gamma2) (v r) in
           - (v gamma2) <= r0_s /\ r0_s <= v gamma2 /\
           (v gamma2 == 95232 ==> 0 <= r1_s /\ r1_s < 44) /\
           (v gamma2 == 261888 ==> 0 <= r1_s /\ r1_s < 16)))
  = let g = v gamma2 in
    let q = 8380417 in
    let twog = g * 2 in
    let r_q = (v r) % q in
    L.lemma_mod_lt (v r) q;
    let r_g = Spec.Utils.mod_p r_q twog in
    L.lemma_mod_lt r_q twog;
    assert (-g < r_g /\ r_g <= g);
    lemma_spec_decompose_r1_bound g (v r)
#pop-options

(* Conditional equation for decompose (paired-lemma template).
   Under `v input ∈ [0, q)`, `Hacspec.decompose` agrees with
   `Spec.MLDSA.Math.decompose` (output layouts differ; v-image agrees).
   Discharges the trait-side `decompose_lane_post`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let lemma_decompose_lane_commute_conditional
    (gamma2 input low_future high_future: i32)
    : Lemma
        (requires
          (v gamma2 == 95232 \/ v gamma2 == 261888) /\
          (let (r0_s, r1_s, _) = Spec.MLDSA.Math.decompose (v gamma2) (v input) in
           v low_future == r0_s /\ v high_future == r1_s))
        (ensures TS.decompose_lane_post gamma2 input low_future high_future)
  = reveal_opaque (`%TS.decompose_lane_post)
                  (TS.decompose_lane_post gamma2 input low_future high_future);
    introduce
        v input >= 0 /\ v input < 8380417 ==>
        (let pair = Hacspec_ml_dsa.Arithmetic.decompose input gamma2 in
         v low_future == v (snd pair) /\ v high_future == v (fst pair))
    with hyp.
      lemma_decompose_bridge input gamma2
#pop-options

(* Bound lemma for compute_hint (paired-lemma template).  Trivial:
   `Spec.MLDSA.Math.compute_one_hint` returns 0 or 1 by definition.
   Used to discharge `is_binary_array_8_opaque hint_future`. *)
let lemma_compute_one_hint_bound (low high gamma2: i32)
    : Lemma
        (let res = Spec.MLDSA.Math.compute_one_hint (v low) (v high) (v gamma2) in
         res == 0 \/ res == 1)
  = ()

(* Bound lemma for the popcount (`Spec.MLDSA.Math.compute_hint`)
   under the binary-hint hypothesis: each of the 8 lanes is 0 or 1,
   so the sum is in [0, 8].  Discharges the trait-side
   `v result <= 8` conjunct on `Operations::compute_hint`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let rec lemma_compute_hint_bound_aux (hint: t_Array i32 (sz 8)) (n: nat{n <= 8})
    : Lemma
        (requires
          (forall (i: nat). i < 8 ==>
            (v (Seq.index hint i) == 0 \/ v (Seq.index hint i) == 1)))
        (ensures
          Spec.Utils.repeati (sz n) (Spec.MLDSA.Math.hint_counter hint) 0 <= n)
        (decreases n)
  = if n = 0 then
      Spec.Utils.eq_repeati0 (sz 0) (Spec.MLDSA.Math.hint_counter hint) 0
    else begin
      lemma_compute_hint_bound_aux hint (n - 1);
      Spec.Utils.unfold_repeati (sz n) (Spec.MLDSA.Math.hint_counter hint) 0 (sz (n - 1));
      // step adds v (cast hint[n-1] <: usize) which is 0 or 1 under hyp.
      assert (v (cast (Seq.index hint (n - 1)) <: usize) == 0 \/
              v (cast (Seq.index hint (n - 1)) <: usize) == 1)
    end
#pop-options

let lemma_compute_hint_bound (hint: t_Array i32 (sz 8))
    : Lemma
        (requires
          (forall (i: nat). i < 8 ==>
            (v (Seq.index hint i) == 0 \/ v (Seq.index hint i) == 1)))
        (ensures Spec.MLDSA.Math.compute_hint hint <= 8)
  = lemma_compute_hint_bound_aux hint 8

(* Conditional equation for compute_hint (paired-lemma template).
   Bridges `Spec.MLDSA.Math.compute_one_hint` to `Hacspec.make_hint`
   under `v high ∈ [0, q)`.  `Spec.compute_one_hint` is a direct
   formula on `low`; `Hacspec.make_hint` calls `high_bits` on `high`
   and `mod_q (high + low)` and tests inequality.  The two are
   equivalent under the trait pre's bounds, but the equivalence is a
   non-trivial FIPS 204 §3.6 property — placeholder admit for now,
   matching the F-1 scaffolding shape. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let lemma_compute_hint_lane_commute_conditional
    (gamma2 low high hint_future: i32)
    : Lemma
        (requires
          (v gamma2 == 95232 \/ v gamma2 == 261888) /\
          v hint_future == Spec.MLDSA.Math.compute_one_hint (v low) (v high) (v gamma2))
        (ensures TS.compute_hint_lane_post gamma2 low high hint_future)
  = reveal_opaque (`%TS.compute_hint_lane_post)
                  (TS.compute_hint_lane_post gamma2 low high hint_future);
    introduce
        v high >= 0 /\ v high < 8380417 ==>
        (if Hacspec_ml_dsa.Arithmetic.make_hint low high gamma2
         then v hint_future == 1
         else v hint_future == 0)
    with hyp.
      admit ()  (* Track 2 follow-up: prove
                   Spec.MLDSA.Math.compute_one_hint (v low) (v high) (v gamma2) == 1
                   <==> Hacspec_ml_dsa.Arithmetic.make_hint low high gamma2.
                   Spec form is a direct |r0|-vs-gamma2 comparison;
                   Hacspec form decomposes both `high` and `mod_q (high + low)`
                   and tests their high-bits.  This is the standard FIPS 204
                   "MakeHint correctness" property — non-trivial proof,
                   estimated 60-100 lines.  Bridge involves showing that
                   |r0| > gamma2 (or boundary case) is equivalent to
                   high_bits changing under +z. *)
#pop-options

(* === Step 12 Track B: AVX2 decompose impl-side bridge === *)

(* Bridge: AVX2 SIMD-shape `Spec.MLDSA.Math.decompose_spec` agrees in
   v-image with the canonical `Spec.MLDSA.Math.decompose` for any
   `v r` in i32-bounded trait range and valid gamma2.  The
   decompose_spec body normalizes negatives via `if r < 0 then r + q`,
   so r' = if v r >= 0 then v r else v r + q ∈ [0, q-1].  This is the
   same value as `(v r) % q` (Euclidean), which is the input that
   `Spec.MLDSA.Math.decompose` consumes.  So the two agree
   unconditionally for v r ∈ [-(q-1), q-1].

   Body: full proof requires showing the bit-trick approximation
   `(r' * 11275 + 2^23) >> 24` (for gamma2 = 95232) and
   `(r' * 1025 + 2^21) >> 22` (for gamma2 = 261888) compute exactly
   `r' / (2*gamma2)` (with the special-case correction at boundary).
   This is a non-trivial bit-trick / interval analysis (~150-200 lines).
   Step 12 lands the structural template with `admit ()` body; the math
   close is deferred to a USER-lane session matching Track 4 mont_mul's
   depth.  Once closed, the AVX2 `Operations::decompose` impl-method
   body (`src/simd/avx2.rs:376`) carries a real proof modulo this
   admit. *)
let lemma_decompose_spec_eq_decompose (gamma2 r: i32)
    : Lemma
        (requires
          (v gamma2 == 95232 \/ v gamma2 == 261888) /\
          Spec.Utils.is_i32b 8380416 r)
        (ensures
          (let (r0_s_avx, r1_s_avx) = Spec.MLDSA.Math.decompose_spec gamma2 r in
           let (r0_int, r1_int, _) = Spec.MLDSA.Math.decompose (v gamma2) (v r) in
           v r0_s_avx == r0_int /\ v r1_s_avx == r1_int))
  = admit ()

(* === Track 4 (Step 9.6 AVX2 montgomery_multiply) === *)

(* Bound + mod-q congruence for `Spec.MLDSA.Math.mont_mul`.

   Mirror of the ML-KEM template `lemma_mont_mul_red_i16_int`
   (`libcrux-ml-kem/proofs/fstar/spec/Spec.Utils.fst:505`) with
   i16→i32, i32→i64, shift 16→32, q=3329→8380417,
   q'=−3327→58728449 (note: ML-DSA stores q' as positive,
   58728449 = q^-1 mod 2^32; ML-KEM stored as -3327 ≡ q^-1 mod 2^16
   due to negation convention), R^-1=169→8265825.

   The Montgomery property `q' * q ≡ 1 (mod R)`:
     58728449 * 8380417 = 4294967296 * 114592 + 1, so the product
     mod 2^32 = 1.  Verified via assert_norm. *)
#push-options "--z3rlimit 600 --fuel 0 --ifuel 1"
let lemma_mont_mul_bound_and_mod_q (x y: i32)
    : Lemma
        (requires Spec.Utils.is_i32b 8380416 y)
        (ensures
          Spec.Utils.is_i32b 8380416 (Spec.MLDSA.Math.mont_mul x y) /\
          (v (Spec.MLDSA.Math.mont_mul x y)) % 8380417 ==
          (v x * v y * 8265825) % 8380417)
  = Spec.Intrinsics.reveal_opaque_arithmetic_ops #i32_inttype;
    Spec.Intrinsics.reveal_opaque_arithmetic_ops #i64_inttype;
    Spec.Intrinsics.reveal_opaque_cast_ops #i32_inttype #i64_inttype;
    reveal_opaque (`%Spec.MLDSA.Math.mont_mul) (Spec.MLDSA.Math.mont_mul x y);
    reveal_opaque (`%Spec.MLDSA.Math.i32_mul) (Spec.MLDSA.Math.i32_mul);
    let prod : int = v x * v y in
    // Step 1: product = i32_mul x y (i64 with v == prod, since |prod| < pow2 63).
    assert_norm (pow2 31 * 8380416 < pow2 63);
    Spec.Utils.lemma_range_at_percent prod (pow2 64);
    let cast_x : i64 = cast x <: i64 in
    let cast_y : i64 = cast y <: i64 in
    Spec.Utils.lemma_range_at_percent (v x) (pow2 64);
    Spec.Utils.lemma_range_at_percent (v y) (pow2 64);
    assert (v cast_x == v x /\ v cast_y == v y);
    let product : i64 = Spec.MLDSA.Math.i32_mul x y in
    assert (v product == prod);
    // Step 2: hi = cast_mod (product >> 32) <: i32 = prod / 2^32.
    let prod_shifted : i64 = product >>! mk_i32 32 in
    assert (v prod_shifted == prod / pow2 32);
    assert_norm (pow2 31 * 8380416 / pow2 32 < pow2 31);
    assert_norm (- (pow2 31 * 8380416 / pow2 32) > - pow2 31);
    Spec.Utils.lemma_range_at_percent (prod / pow2 32) (pow2 32);
    let hi : i32 = cast prod_shifted <: i32 in
    assert (v hi == prod / pow2 32);
    // Step 3: low = cast_mod product <: i32 = prod @% 2^32.
    let low : i32 = cast product <: i32 in
    assert (v low == prod @% pow2 32);
    // Step 4: k = cast_mod (low *! Q' as i64) <: i32 = (low * Q') @% 2^32.
    let q'_i32 = mk_i32 58728449 in
    let cast_low : i64 = cast low <: i64 in
    let cast_qp : i64 = cast q'_i32 <: i64 in
    Spec.Utils.lemma_range_at_percent (v low) (pow2 64);
    Spec.Utils.lemma_range_at_percent 58728449 (pow2 64);
    assert (v cast_low == v low /\ v cast_qp == 58728449);
    let lq_product : i64 = Spec.MLDSA.Math.i32_mul low q'_i32 in
    assert_norm (pow2 31 * 58728449 < pow2 63);
    Spec.Utils.lemma_range_at_percent (v low * 58728449) (pow2 64);
    assert (v lq_product == v low * 58728449);
    let k : i32 = cast lq_product <: i32 in
    assert (v k == (v low * 58728449) @% pow2 32);
    // Step 5: c = cast_mod ((k * Q as i64) >> 32) <: i32 = (k*q)/2^32 (under bound).
    let q_i32 = mk_i32 8380417 in
    let cast_k : i64 = cast k <: i64 in
    let cast_q : i64 = cast q_i32 <: i64 in
    Spec.Utils.lemma_range_at_percent (v k) (pow2 64);
    Spec.Utils.lemma_range_at_percent 8380417 (pow2 64);
    assert (v cast_k == v k /\ v cast_q == 8380417);
    let kq_product : i64 = Spec.MLDSA.Math.i32_mul k q_i32 in
    assert_norm (pow2 31 * 8380417 < pow2 63);
    Spec.Utils.lemma_range_at_percent (v k * 8380417) (pow2 64);
    assert (v kq_product == v k * 8380417);
    let kq_shifted : i64 = kq_product >>! mk_i32 32 in
    assert (v kq_shifted == (v k * 8380417) / pow2 32);
    assert_norm (pow2 31 * 8380417 / pow2 32 < pow2 31);
    assert_norm (- (pow2 31 * 8380417 / pow2 32) > - pow2 31);
    Spec.Utils.lemma_range_at_percent ((v k * 8380417) / pow2 32) (pow2 32);
    let c : i32 = cast kq_shifted <: i32 in
    assert (v c == (v k * 8380417) / pow2 32);
    // Step 6: result = sub_mod hi c.  Bound preservation needs |hi - c| < 2^31.
    assert_norm (pow2 22 + (pow2 31 * 8380417 / pow2 32) < pow2 31);
    let result : i32 = hi -! c in
    assert (v result == v hi - v c);
    // === MOD-q PROOF (mirroring ML-KEM's calc chain) ===
    // Show: (k * q) % 2^32 == prod % 2^32  (so prod - k*q is divisible by 2^32).
    assert_norm ((58728449 * 8380417) % pow2 32 == 1);
    Spec.Utils.lemma_at_percent_mod (v low * 58728449) (pow2 32);
    // (v k) * 8380417 ≡ ((v low * 58728449) @% 2^32) * 8380417 (mod 2^32)
    // Apply lemma_mod_mul_distr_l to push @% inside:
    L.lemma_mod_mul_distr_l (v low * 58728449) 8380417 (pow2 32);
    L.lemma_mod_mul_distr_l ((v low * 58728449) @% pow2 32) 8380417 (pow2 32);
    Spec.Utils.lemma_at_percent_mod (v low * 58728449) (pow2 32);
    // Now: (v k * 8380417) % 2^32 == (v low * 58728449 * 8380417) % 2^32
    //                            == (v low * 1) % 2^32  (using q'*q ≡ 1 mod 2^32)
    //                            == v low % 2^32
    //                            == prod % 2^32
    L.lemma_mod_mul_distr_r (v low) (58728449 * 8380417) (pow2 32);
    Spec.Utils.lemma_at_percent_mod prod (pow2 32);
    assert ((v k * 8380417) % pow2 32 == prod % pow2 32);
    // (prod - k*q) % 2^32 == 0:
    L.lemma_mod_sub_distr prod (v k * 8380417) (pow2 32);
    assert ((prod - v k * 8380417) % pow2 32 == 0);
    L.lemma_div_exact (prod - v k * 8380417) (pow2 32);
    // hi - c = prod/2^32 - (k*q)/2^32 = (prod - k*q)/2^32 (using lemma_div_exact).
    assert (v result == (prod - v k * 8380417) / pow2 32);
    // Final step: ((prod - k*q)/2^32) % q == (prod * 8265825) % q.
    assert_norm ((pow2 32 * 8265825) % 8380417 == 1);
    L.lemma_mod_mul_distr_r ((prod - v k * 8380417) / pow2 32) (pow2 32 * 8265825) 8380417;
    L.lemma_div_exact (prod - v k * 8380417) (pow2 32);
    L.lemma_mod_sub (prod * 8265825) 8380417 (v k * 8265825);
    // === BOUND PROOF: |v result| ≤ q-1 = 8380416 ===
    // |hi| ≤ pow2 22 (since |prod| ≤ pow2 31 * 8380416 < pow2 54, /pow2 32 < pow2 22).
    // |c| ≤ pow2 31 * 8380417 / pow2 32 ≈ 2^22.  Combined |hi - c| < q from Montgomery.
    // The tight bound: |v result * pow2 32| = |prod - k*q|.
    //   |prod| < pow2 31 * 8380416 < (pow2 31) * q
    //   |v k| < pow2 31 (i32 range), |v k * q| < pow2 31 * q
    //   |prod - k*q| < 2 * pow2 31 * q = pow2 32 * q
    //   |v result| < pow2 32 * q / pow2 32 = q, i.e., |v result| ≤ q-1.
    assert (v product == prod);  // anchor
    assert_norm (pow2 31 * 8380417 + pow2 31 * 8380416 < pow2 32 * 8380417)
#pop-options
