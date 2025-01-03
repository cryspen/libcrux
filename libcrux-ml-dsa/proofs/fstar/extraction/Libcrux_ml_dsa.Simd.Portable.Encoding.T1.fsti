module Libcrux_ml_dsa.Simd.Portable.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val deserialize (serialized: t_Slice u8) (simd_unit: t_Array i32 (sz 8))
    : Prims.Pure (t_Array i32 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val serialize (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
