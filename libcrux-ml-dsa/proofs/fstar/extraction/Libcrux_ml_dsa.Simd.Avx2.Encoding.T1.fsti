module Libcrux_ml_dsa.Simd.Avx2.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize__COEFFICIENT_MASK: i32 = (1l <<! 10l <: i32) -! 1l

val serialize (simd_unit: u8) : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize (bytes: t_Slice u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
