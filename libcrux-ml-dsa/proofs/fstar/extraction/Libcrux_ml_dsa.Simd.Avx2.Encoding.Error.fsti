module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_to_unsigned_when_eta_is_2___COEFFICIENT_MASK: i32 = (1l <<! 3l <: i32) -! 1l

let deserialize_to_unsigned_when_eta_is_4___COEFFICIENT_MASK: i32 = (1l <<! 4l <: i32) -! 1l

let serialize_when_eta_is_2___ETA: i32 = 2l

let serialize_when_eta_is_4___ETA: i32 = 4l

val deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_to_unsigned (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (serialized: t_Slice u8)
      (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_eta_is_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_eta_is_4_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

val serialize
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (serialized: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)
