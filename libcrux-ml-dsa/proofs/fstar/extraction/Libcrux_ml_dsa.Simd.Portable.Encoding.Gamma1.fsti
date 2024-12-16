module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = 1l <<! 17l

let deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___GAMMA1 <<! 1l <: i32) -! 1l

let deserialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = 1l <<! 19l

let deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___GAMMA1 <<! 1l <: i32) -! 1l

let serialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = 1l <<! 17l

let serialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = 1l <<! 19l

val deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_17_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_19_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize
      (v_GAMMA1_EXPONENT: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
