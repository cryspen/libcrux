module Libcrux_ml_dsa.Simd.Avx2.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val change_interval (simd_unit: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

let deserialize__COEFFICIENT_MASK: i32 = (1l <<! 13l <: i32) -! 1l

val deserialize (serialized: t_Slice u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val serialize (simd_unit: u8) : Prims.Pure (t_Array u8 (sz 13)) Prims.l_True (fun _ -> Prims.l_True)
