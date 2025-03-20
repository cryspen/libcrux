module Libcrux_ml_dsa.Specs.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let rejection_sample_less_than_field_modulus_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  b2t
  ((((Core.Slice.impl__len #u8 randomness <: usize) /! mk_usize 3 <: usize) <=. mk_usize 4294967295
      <:
      bool) &&
    (((Core.Slice.impl__len #u8 randomness <: usize) /! mk_usize 3 <: usize) <=.
      (Core.Slice.impl__len #i32 out <: usize)
      <:
      bool))

let rejection_sample_less_than_field_modulus_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_field_modulus randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s

let rejection_sample_less_than_eta_equals_2_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  b2t
  ((((Core.Slice.impl__len #u8 randomness <: usize) *! mk_usize 2 <: usize) <=. mk_usize 4294967295
      <:
      bool) &&
    (((Core.Slice.impl__len #u8 randomness <: usize) *! mk_usize 2 <: usize) <=.
      (Core.Slice.impl__len #i32 out <: usize)
      <:
      bool))

let rejection_sample_less_than_eta_equals_2_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_eta_2 randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s

let rejection_sample_less_than_eta_equals_4_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  b2t
  ((((Core.Slice.impl__len #u8 randomness <: usize) *! mk_usize 2 <: usize) <=. mk_usize 4294967295
      <:
      bool) &&
    (((Core.Slice.impl__len #u8 randomness <: usize) *! mk_usize 2 <: usize) <=.
      (Core.Slice.impl__len #i32 out <: usize)
      <:
      bool))

let rejection_sample_less_than_eta_equals_4_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_eta_4 randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s
