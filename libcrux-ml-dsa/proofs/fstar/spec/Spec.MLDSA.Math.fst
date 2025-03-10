module Spec.MLDSA.Math
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core

let rejection_sample_coefficient (randomness:Seq.seq u8) (i:nat{i < (Seq.length randomness) / 3}) : Tot (i32) =
  let b0 = cast (Seq.index randomness (i * 3)) <: i32 in
  let b1 = cast (Seq.index randomness (i * 3 + 1)) <: i32 in
  let b2 = cast (Seq.index randomness (i * 3 + 2)) <: i32 in
  let b2' = if b2 >. mk_i32 127 then b2 -. mk_i32 128  else b2 in
  ((mk_i32 (pow2 16) *. b2') +. (mk_i32 (pow2 8) *. b1)) +. b0

let rejection_sample_field_modulus_inner1
  (randomness:Seq.seq u8)
  (i:nat{i < (Seq.length randomness) / 3})
  s : (Seq.seq i32) =
  s

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
