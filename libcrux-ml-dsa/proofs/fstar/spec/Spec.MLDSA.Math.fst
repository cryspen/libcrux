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

let rejection_sample_coefficient (randomness:Seq.seq u8) (i:nat{i < (Seq.length randomness) / 3}) : Tot (i32) =
  let b0 = cast (Seq.index randomness (i * 3)) <: i32 in
  let b1 = cast (Seq.index randomness (i * 3 + 1)) <: i32 in
  let b2 = cast (Seq.index randomness (i * 3 + 2)) <: i32 in
  let b2' = if b2 >. mk_i32 127 then b2 -. mk_i32 128  else b2 in
  ((mk_i32 (pow2 16) *. b2') +. (mk_i32 (pow2 8) *. b1)) +. b0

let rejection_sample_field_modulus_inner
  (randomness:Seq.seq u8)
  (i:nat{i < (Seq.length randomness) / 3})
  s : (Seq.seq i32) =
  let coefficient = rejection_sample_coefficient randomness i in
  if coefficient <. mk_i32 8380417 then 
    Seq.append s (Seq.create 1 coefficient) else s

let rejection_sample_field_modulus (randomness:Seq.seq u8) : (Seq.seq i32) =
  Lib.LoopCombinators.repeati ((Seq.length randomness) / 3)
    (rejection_sample_field_modulus_inner randomness) Seq.empty

let rejection_sample_eta_2_inner
  (randomness:Seq.seq u8)
  (i:nat{i < Seq.length randomness})
  s : (Seq.seq i32) =
  let byte = Seq.index randomness i in
  let try_0 = byte &. mk_u8 15 in
  let try_1 = byte >>! mk_u8 4 in
  let s = if try_0 <. mk_u8 15 then 
    Seq.append s (Seq.create 1 (mk_i32 2 -. ((cast try_0 <: i32) %! mk_i32 5))) else s in
  if try_1 <. mk_u8 15 then 
    Seq.append s (Seq.create 1 (mk_i32 2 -. ((cast try_1 <: i32) %! mk_i32 5))) else s

let rejection_sample_eta_2 (randomness:Seq.seq u8) : (Seq.seq i32) =
  Lib.LoopCombinators.repeati (Seq.length randomness)
    (rejection_sample_eta_2_inner randomness) Seq.empty

let rejection_sample_eta_4_inner
  (randomness:Seq.seq u8)
  (i:nat{i < Seq.length randomness})
  s : (Seq.seq i32) =
  let byte = Seq.index randomness i in
  let try_0 = byte &. mk_u8 15 in
  let try_1 = byte >>! mk_u8 4 in
  let s = if try_0 <. mk_u8 9 then 
    Seq.append s (Seq.create 1 (mk_i32 4 -. (cast try_0 <: i32))) else s in
  if try_1 <. mk_u8 9 then 
    Seq.append s (Seq.create 1 (mk_i32 4 -. (cast try_1 <: i32))) else s

let rejection_sample_eta_4 (randomness:Seq.seq u8) : (Seq.seq i32) =
  Lib.LoopCombinators.repeati (Seq.length randomness)
    (rejection_sample_eta_4_inner randomness) Seq.empty

#push-options "--z3rlimit 1500 --fuel 3 --ifuel 3 --ext context_pruning --z3refresh"

let rejection_sample_coefficient_lemma (randomness:Seq.seq u8) (i:nat{i < (Seq.length randomness) / 3}) :
  Lemma (let b0 = cast (Seq.index randomness (i * 3)) <: i32 in
        let b1 = cast (Seq.index randomness (i * 3 + 1)) <: i32 in
        let b2 = cast (Seq.index randomness (i * 3 + 2)) <: i32 in
        let coefficient = (((b2 <<! mk_i32 16) |. (b1 <<! mk_i32 8)) |. b0) &.
            mk_i32 8388607 in
        Spec.MLDSA.Math.rejection_sample_coefficient randomness i == coefficient) =
  let b0 = cast (Seq.index randomness (i * 3)) <: i32 in
  let b1 = cast (Seq.index randomness (i * 3 + 1)) <: i32 in
  let b2 = cast (Seq.index randomness (i * 3 + 2)) <: i32 in
  let b2' = if b2 >. mk_i32 127 then b2 -. mk_i32 128  else b2 in
  assert_norm (pow2 23 == 8388608);
  assert (b2' == (b2 %! mk_i32 128));
  assert (((mk_i32 (pow2 16) *. b2) %! mk_i32 (pow2 23)) == (mk_i32 (pow2 16) *. (b2 %! mk_i32 128)));
  logor_disjoint (b2 <<! mk_i32 16) (b1 <<! mk_i32 8) 16;
  assert (((b2 <<! mk_i32 16) |. (b1 <<! mk_i32 8)) == ((b2 <<! mk_i32 16) +. (b1 <<! mk_i32 8)));
  logor_disjoint ((b2 <<! mk_i32 16) |. (b1 <<! mk_i32 8)) b0 8;
  assert ((((b2 <<! mk_i32 16) |. (b1 <<! mk_i32 8)) |. b0) ==
    (((b2 <<! mk_i32 16) +. (b1 <<! mk_i32 8)) +. b0));
  assert ((b2 <<! mk_i32 16) == (mk_i32 (pow2 16) *. b2));
  assert ((b1 <<! mk_i32 8) == (mk_i32 (pow2 8) *. b1));
  logand_mask_lemma (((mk_i32 (pow2 16) *. b2) +. (mk_i32 (pow2 8) *. b1)) +. b0) 23;
  assert (((((mk_i32 (pow2 16) *. b2) +. ((mk_i32 (pow2 8) *. b1)) +. b0)) %! mk_i32 (pow2 23)) ==
    ((((mk_i32 (pow2 16) *. b2) %! mk_i32 (pow2 23)) +. ((mk_i32 (pow2 8) *. b1)) +. b0)));
  assert (((((mk_i32 (pow2 16) *. b2) +. (mk_i32 (pow2 8) *. b1)) +. b0) %! mk_i32 (pow2 23)) ==
    (((mk_i32 (pow2 16) *. (b2 %! mk_i32 128)) +. (mk_i32 (pow2 8) *. b1)) +. b0));
  assert (((((mk_i32 (pow2 16) *. b2) +. (mk_i32 (pow2 8) *. b1)) +. b0) %! mk_i32 (pow2 23)) ==
    (((mk_i32 (pow2 16) *. b2') +. (mk_i32 (pow2 8) *. b1)) +. b0))

#pop-options
