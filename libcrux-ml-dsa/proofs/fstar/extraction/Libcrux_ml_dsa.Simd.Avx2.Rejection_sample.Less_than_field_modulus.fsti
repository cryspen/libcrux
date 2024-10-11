module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let bytestream_to_potential_coefficients__COEFFICIENT_MASK: i32 =
  (Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 23 <: i32) -! Rust_primitives.mk_i32 1

val bytestream_to_potential_coefficients (serialized: t_Slice u8)
    : Prims.Pure Libcrux_intrinsics.Avx2_extract.t_Vec256 Prims.l_True (fun _ -> Prims.l_True)

val sample (input: t_Slice u8) (output: t_Slice i32)
    : Prims.Pure (t_Slice i32 & usize) Prims.l_True (fun _ -> Prims.l_True)
