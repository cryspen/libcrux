module Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let deserialize_when_gamma1_is_2_pow_17___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 17

let deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___GAMMA1 <<! Rust_primitives.mk_i32 1 <: i32) -!
  Rust_primitives.mk_i32 1

let deserialize_when_gamma1_is_2_pow_19___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 19

let deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_MASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___GAMMA1 <<! Rust_primitives.mk_i32 1 <: i32) -!
  Rust_primitives.mk_i32 1

let serialize_when_gamma1_is_2_pow_17___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 17

let serialize_when_gamma1_is_2_pow_19___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 19

val deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val deserialize (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_17_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_19_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)
