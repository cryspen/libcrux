module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Seq.length randomness / 3 <= Lib.IntTypes.max_size_t /\
        Seq.length randomness / 3 <= Seq.length out)
      (ensures
        fun temp_0_ ->
          let out_future, result:(t_Slice i32 & usize) = temp_0_ in
          let s = Spec.MLDSA.Math.rejection_sample_field_modulus randomness in
          v result <= Seq.length out_future /\ v result == Seq.length s /\
          Seq.slice out_future 0 (v result) == s)

val rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
        Seq.length randomness * 2 <= Seq.length out)
      (ensures
        fun temp_0_ ->
          let out_future, result:(t_Slice i32 & usize) = temp_0_ in
          let s = Spec.MLDSA.Math.rejection_sample_eta_2 randomness in
          v result <= Seq.length out_future /\ v result == Seq.length s /\
          Seq.slice out_future 0 (v result) == s)

val rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Seq.length randomness * 2 <= Lib.IntTypes.max_size_t /\
        Seq.length randomness * 2 <= Seq.length out)
      (ensures
        fun temp_0_ ->
          let out_future, result:(t_Slice i32 & usize) = temp_0_ in
          let s = Spec.MLDSA.Math.rejection_sample_eta_4 randomness in
          v result <= Seq.length out_future /\ v result == Seq.length s /\
          Seq.slice out_future 0 (v result) == s)
