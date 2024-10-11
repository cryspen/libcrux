module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta3
      (Rust_primitives.mk_i32 0)
      zeta2
      (Rust_primitives.mk_i32 0)
      zeta1
      (Rust_primitives.mk_i32 0)
      zeta0
      (Rust_primitives.mk_i32 0)
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 177) simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (Rust_primitives.mk_i32 170) sums products

let invert_ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1
      zeta1
      (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 0)
      zeta0
      zeta0
      (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 0)
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 1)
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 78) simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (Rust_primitives.mk_i32 204) sums products

let invert_ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta
      zeta
      zeta
      zeta
      (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 0)
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 (-1))
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 1)
      (Rust_primitives.mk_i32 1)
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (Rust_primitives.mk_i32 78) simd_unit
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 add_by add_by_signs
  in
  let sums:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 simd_unit add_by
  in
  let products:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply sums zetas
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 (Rust_primitives.mk_i32 240) sums products

let ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Core.Ops.Arith.Neg.neg zeta3 <: i32)
      zeta3
      (Core.Ops.Arith.Neg.neg zeta2 <: i32)
      zeta2
      (Core.Ops.Arith.Neg.neg zeta1 <: i32)
      zeta1
      (Core.Ops.Arith.Neg.neg zeta0 <: i32)
      zeta0
  in
  let zeta_multipliers:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 245) simd_unit
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 160) simd_unit
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 rhs lhs

let ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Core.Ops.Arith.Neg.neg zeta1 <: i32)
      (Core.Ops.Arith.Neg.neg zeta1 <: i32)
      zeta1
      zeta1
      (Core.Ops.Arith.Neg.neg zeta0 <: i32)
      (Core.Ops.Arith.Neg.neg zeta0 <: i32)
      zeta0
      zeta0
  in
  let zeta_multipliers:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 238) simd_unit
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (Rust_primitives.mk_i32 68) simd_unit
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 rhs lhs

let ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Core.Ops.Arith.Neg.neg zeta <: i32)
      (Core.Ops.Arith.Neg.neg zeta <: i32)
      (Core.Ops.Arith.Neg.neg zeta <: i32)
      (Core.Ops.Arith.Neg.neg zeta <: i32)
      zeta
      zeta
      zeta
      zeta
  in
  let zeta_multipliers:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (Rust_primitives.mk_i32 238) simd_unit
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (Rust_primitives.mk_i32 68) simd_unit
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 rhs lhs
