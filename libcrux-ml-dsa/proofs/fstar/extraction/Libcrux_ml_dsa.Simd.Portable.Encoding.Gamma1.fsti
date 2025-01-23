module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = mk_i32 1 <<! mk_i32 17

let deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

let deserialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = mk_i32 1 <<! mk_i32 19

let deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___GAMMA1 <<! mk_i32 1 <: i32) -! mk_i32 1

let serialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = mk_i32 1 <<! mk_i32 17

let serialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = mk_i32 1 <<! mk_i32 19

val deserialize_when_gamma1_is_2_pow_17_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_when_gamma1_is_2_pow_19_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize
      (serialized: t_Slice u8)
      (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma1_exponent: usize)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_17_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_19_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
      (gamma1_exponent: usize)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
