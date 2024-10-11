module Libcrux_ml_dsa.Simd.Avx2.Encoding.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_to_unsigned_when_eta_is_2___COEFFICIENT_MASK: i32 =
  (Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 3 <: i32) -! Rust_primitives.mk_i32 1

let deserialize_to_unsigned_when_eta_is_4___COEFFICIENT_MASK: i32 =
  (Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 4 <: i32) -! Rust_primitives.mk_i32 1

let serialize_when_eta_is_2___ETA: i32 = Rust_primitives.mk_i32 2

let serialize_when_eta_is_4___ETA: i32 = Rust_primitives.mk_i32 4

val deserialize_to_unsigned_when_eta_is_2_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_to_unsigned_when_eta_is_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_to_unsigned (v_ETA: usize) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize (v_ETA: usize) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_eta_is_2_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_eta_is_4_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)
