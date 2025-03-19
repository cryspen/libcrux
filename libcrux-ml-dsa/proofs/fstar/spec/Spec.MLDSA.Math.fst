module Spec.MLDSA.Math
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core

include Spec.Utils

let v_FIELD_MODULUS: i32 = mk_i32 8380417

let v_BITS_IN_LOWER_PART_OF_T: usize = mk_usize 13

let v_GAMMA2_V261_888: i32 = mk_i32 261888
let v_GAMMA2_V95_232: i32 = mk_i32 95232
let is_gamma2 (g:range_t I32) = g == v v_GAMMA2_V261_888 \/ g == v v_GAMMA2_V95_232

type gamma2 = g:range_t I32{is_gamma2 g}

let power2round (t:range_t I32) : (range_t I32 & range_t I32) =
  let t0 = mod_p (t % v v_FIELD_MODULUS) (pow2 (v v_BITS_IN_LOWER_PART_OF_T)) in
  let t1 = ((t % v v_FIELD_MODULUS) - t0) / pow2 (v v_BITS_IN_LOWER_PART_OF_T) in
  (t0, t1)

let decompose (g:gamma2) (r:range_t I32) : (range_t I32 & range_t I32 & bool) =
  let r_q = r % v v_FIELD_MODULUS in
  let r_g = mod_p r_q (g * 2) in
  if r_q - r_g = v v_FIELD_MODULUS - 1 then
    (r_g - 1, 0, true)
  else
    (r_g, (r_q - r_g) / (g * 2), false)

let compute_one_hint (low high gamma2:range_t I32) : (range_t I32) =
  if low > gamma2 || low < -(gamma2) || (low = -(gamma2) && high <> 0)
  then 1 else 0

let use_one_hint (g:gamma2) (r:range_t I32) (hint:range_t I32{hint == 0 \/ hint == 1}) : (range_t I32) =
  let r0, r1, _ = decompose g r in
  if hint = 0 then
    r1
  else
    (if r0 > 0 then
      (r1 + 1) % (4190208 / g)
    else
      (r1 - 1) % (4190208 / g))

let hint_counter (hint:t_Array i32 (mk_usize 8)) (i:nat{i < 8}) (s:nat) : Tot (nat) =
  s + v (cast hint.[sz i] <: usize)

val hint_counter_loop:
  hint_1:t_Array i32 (mk_usize 8)
  -> hint_2:t_Array i32 (mk_usize 8)
  -> n:nat{n < 8} ->
  Lemma
   (requires
      forall (i:nat). i < n ==> hint_1.[mk_usize i] == hint_2.[mk_usize i])
    (ensures
      Lib.LoopCombinators.repeati n (hint_counter hint_1) 0 ==
        Lib.LoopCombinators.repeati n (hint_counter hint_2) 0)

let rec hint_counter_loop hint_1 hint_2 n =
  if n = 0 then begin
    Lib.LoopCombinators.eq_repeati0 n (hint_counter hint_1) 0;
    Lib.LoopCombinators.eq_repeati0 n (hint_counter hint_2) 0;
    () end
  else begin
    hint_counter_loop hint_1 hint_2 (n - 1);
    Lib.LoopCombinators.unfold_repeati n (hint_counter hint_1) 0 (n - 1);
    Lib.LoopCombinators.unfold_repeati n (hint_counter hint_2) 0 (n - 1);
    () end

let compute_hint (hint:t_Array i32 (mk_usize 8)) : nat =
  Lib.LoopCombinators.repeati 8 (hint_counter hint) 0
