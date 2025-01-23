module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize) Prims.l_True (fun _ -> Prims.l_True)

val rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize) Prims.l_True (fun _ -> Prims.l_True)
