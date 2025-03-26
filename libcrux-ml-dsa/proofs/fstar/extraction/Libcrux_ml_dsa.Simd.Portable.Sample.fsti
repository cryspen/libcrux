module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_field_modulus_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_field_modulus_post randomness
            out_future
            r)

val rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_post randomness
            out_future
            r)

val rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize)
      (requires
        Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_pre randomness
          out)
      (ensures
        fun temp_0_ ->
          let out_future, r:(t_Slice i32 & usize) = temp_0_ in
          Libcrux_ml_dsa.Specs.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_post randomness
            out_future
            r)
