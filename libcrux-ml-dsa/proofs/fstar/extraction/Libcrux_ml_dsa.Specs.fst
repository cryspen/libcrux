module Libcrux_ml_dsa.Specs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let rejection_sample_less_than_field_modulus_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  Seq.length randomness / 3 <= Lib.IntTypes.max_size_t /\
  Seq.length randomness / 3 <= Seq.length out

let rejection_sample_less_than_field_modulus_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_field_modulus randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s

let rejection_sample_less_than_eta_equals_2_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
  Seq.length randomness * 2 <= Seq.length out

let rejection_sample_less_than_eta_equals_2_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_eta_2 randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s

let rejection_sample_less_than_eta_equals_4_pre (randomness: t_Slice u8) (out: t_Slice i32)
    : Hax_lib.Prop.t_Prop =
  Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
  Seq.length randomness * 2 <= Seq.length out

let rejection_sample_less_than_eta_equals_4_post
      (randomness: t_Slice u8)
      (out: t_Slice i32)
      (r: usize)
    : Hax_lib.Prop.t_Prop =
  let s = Spec.MLDSA.Math.rejection_sample_eta_4 randomness in
  v r <= Seq.length out /\ v r == Seq.length s /\ Seq.slice out 0 (v r) == s
