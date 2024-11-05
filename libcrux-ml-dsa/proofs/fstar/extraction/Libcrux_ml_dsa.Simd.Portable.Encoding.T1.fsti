module Libcrux_ml_dsa.Simd.Portable.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

val deserialize (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)
