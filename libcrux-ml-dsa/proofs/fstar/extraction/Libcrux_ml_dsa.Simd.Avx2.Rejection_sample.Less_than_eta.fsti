module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val shift_interval (v_ETA: usize) (coefficients: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val sample (v_ETA: usize) (input: t_Slice u8) (output: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize) Prims.l_True (fun _ -> Prims.l_True)
