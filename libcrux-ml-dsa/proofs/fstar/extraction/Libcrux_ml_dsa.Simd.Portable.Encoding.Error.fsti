module Libcrux_ml_dsa.Simd.Portable.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_eta_is_2___ETA: i32 = 2l

let deserialize_when_eta_is_4___ETA: i32 = 4l

let serialize_when_eta_is_2___ETA: i32 = 2l

let serialize_when_eta_is_4___ETA: i32 = 4l

val deserialize_when_eta_is_2_
      (serialized: t_Slice u8)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_when_eta_is_4_
      (serialized: t_Slice u8)
      (simd_units: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_when_eta_is_2_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_eta_is_4_
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
