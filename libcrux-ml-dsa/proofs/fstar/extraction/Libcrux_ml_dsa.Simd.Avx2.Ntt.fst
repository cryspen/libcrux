module Libcrux_ml_dsa.Simd.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let invert_ntt_at_layer_0_
      (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i32)
     =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta3 0l zeta2 0l zeta1 0l zeta0 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) 1l (-1l) 1l (-1l) 1l (-1l) 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 177l simd_unit
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
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 170l sums products

let invert_ntt_at_layer_1_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta1 zeta1 0l 0l zeta0 zeta0 0l 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) (-1l) 1l 1l (-1l) (-1l) 1l 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 78l simd_unit
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
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 204l sums products

let invert_ntt_at_layer_2_ (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i32) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 zeta zeta zeta zeta 0l 0l 0l 0l
  in
  let add_by_signs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (-1l) (-1l) (-1l) (-1l) 1l 1l 1l 1l
  in
  let add_by:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 78l simd_unit
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
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi32 240l sums products

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
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l simd_unit
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 160l simd_unit
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
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 238l simd_unit
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 68l simd_unit
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
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 238l simd_unit
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply zeta_multipliers zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 68l simd_unit
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 rhs lhs
