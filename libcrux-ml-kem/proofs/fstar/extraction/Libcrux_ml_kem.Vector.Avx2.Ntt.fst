module Libcrux_ml_kem.Vector.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (Core.Ops.Arith.f_neg zeta3 <: i16)
      (Core.Ops.Arith.f_neg zeta3 <: i16) zeta3 zeta3 (Core.Ops.Arith.f_neg zeta2 <: i16)
      (Core.Ops.Arith.f_neg zeta2 <: i16) zeta2 zeta2 (Core.Ops.Arith.f_neg zeta1 <: i16)
      (Core.Ops.Arith.f_neg zeta1 <: i16) zeta1 zeta1 (Core.Ops.Arith.f_neg zeta0 <: i16)
      (Core.Ops.Arith.f_neg zeta0 <: i16) zeta0 zeta0
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants rhs zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 160) vector
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16) =
  let zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (Core.Ops.Arith.f_neg zeta1 <: i16)
      (Core.Ops.Arith.f_neg zeta1 <: i16) (Core.Ops.Arith.f_neg zeta1 <: i16)
      (Core.Ops.Arith.f_neg zeta1 <: i16) zeta1 zeta1 zeta1 zeta1
      (Core.Ops.Arith.f_neg zeta0 <: i16) (Core.Ops.Arith.f_neg zeta0 <: i16)
      (Core.Ops.Arith.f_neg zeta0 <: i16) (Core.Ops.Arith.f_neg zeta0 <: i16) zeta0 zeta0 zeta0
      zeta0
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 238) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants rhs zetas
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 68) vector
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16) =
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_m128i_by_constants rhs
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 zeta
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_add_epi16 lhs rhs
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 lhs rhs
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients
  in
  Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 (mk_i32 1) combined upper_coefficients

#push-options "--admit_smt_queries true"

let inv_ntt_layer_1_step
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 245) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 (mk_i32 160) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 (-1)) (mk_i16 (-1)) (mk_i16 1)
          (mk_i16 1) (mk_i16 (-1)) (mk_i16 (-1)) (mk_i16 1) (mk_i16 1) (mk_i16 (-1)) (mk_i16 (-1))
          (mk_i16 1) (mk_i16 1) (mk_i16 (-1)) (mk_i16 (-1)) (mk_i16 1) (mk_i16 1)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let sum:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs
  in
  let sum_times_zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants sum
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 zeta3 zeta3 (mk_i16 0) (mk_i16 0) zeta2 zeta2
          (mk_i16 0) (mk_i16 0) zeta1 zeta1 (mk_i16 0) (mk_i16 0) zeta0 zeta0 (mk_i16 0) (mk_i16 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let sum:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.barrett_reduce sum
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 (mk_i32 204) sum sum_times_zetas

#pop-options

let inv_ntt_layer_2_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1: i16) =
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 245) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 160) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (mk_i16 (-1)) (mk_i16 (-1)) (mk_i16 (-1))
          (mk_i16 (-1)) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 (-1)) (mk_i16 (-1))
          (mk_i16 (-1)) (mk_i16 (-1)) (mk_i16 1) (mk_i16 1) (mk_i16 1) (mk_i16 1)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let sum:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs
  in
  let sum_times_zetas:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants sum
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 zeta1 zeta1 zeta1 zeta1 (mk_i16 0) (mk_i16 0)
          (mk_i16 0) (mk_i16 0) zeta0 zeta0 zeta0 zeta0 (mk_i16 0) (mk_i16 0) (mk_i16 0) (mk_i16 0)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 (mk_i32 240) sum sum_times_zetas

let inv_ntt_layer_3_step (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta: i16) =
  let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) vector
  in
  let rhs:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector
  in
  let lower_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_add_epi16 lhs rhs
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 lhs rhs
  in
  let upper_coefficients:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_m128i_by_constants upper_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 zeta
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let combined:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients
  in
  Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 (mk_i32 1) combined upper_coefficients

#push-options "--admit_smt_queries true"

let ntt_multiply (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) (zeta0 zeta1 zeta2 zeta3: i16) =
  let shuffle_with:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 15) (mk_i8 14) (mk_i8 11) (mk_i8 10)
      (mk_i8 7) (mk_i8 6) (mk_i8 3) (mk_i8 2) (mk_i8 13) (mk_i8 12) (mk_i8 9) (mk_i8 8) (mk_i8 5)
      (mk_i8 4) (mk_i8 1) (mk_i8 0) (mk_i8 15) (mk_i8 14) (mk_i8 11) (mk_i8 10) (mk_i8 7) (mk_i8 6)
      (mk_i8 3) (mk_i8 2) (mk_i8 13) (mk_i8 12) (mk_i8 9) (mk_i8 8) (mk_i8 5) (mk_i8 4) (mk_i8 1)
      (mk_i8 0)
  in
  let lhs_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 lhs shuffle_with
  in
  let lhs_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 216) lhs_shuffled
  in
  let lhs_evens:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 lhs_shuffled
  in
  let lhs_evens:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 lhs_evens
  in
  let lhs_odds:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) lhs_shuffled
  in
  let lhs_odds:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 lhs_odds
  in
  let rhs_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 rhs shuffle_with
  in
  let rhs_shuffled:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 (mk_i32 216) rhs_shuffled
  in
  let rhs_evens:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 rhs_shuffled
  in
  let rhs_evens:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 rhs_evens
  in
  let rhs_odds:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 (mk_i32 1) rhs_shuffled
  in
  let rhs_odds:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 rhs_odds
  in
  let left:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 lhs_evens rhs_evens
  in
  let right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 lhs_odds rhs_odds
  in
  let right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s right
  in
  let right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 right
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Core.Ops.Arith.f_neg (cast (zeta3 <: i16)
                <:
                i32)
            <:
            i32)
          (cast (zeta3 <: i16) <: i32)
          (Core.Ops.Arith.f_neg (cast (zeta2 <: i16) <: i32) <: i32)
          (cast (zeta2 <: i16) <: i32)
          (Core.Ops.Arith.f_neg (cast (zeta1 <: i16) <: i32) <: i32)
          (cast (zeta1 <: i16) <: i32)
          (Core.Ops.Arith.f_neg (cast (zeta0 <: i16) <: i32) <: i32)
          (cast (zeta0 <: i16) <: i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let products_left:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 left right
  in
  let products_left:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s products_left
  in
  let rhs_adjacent_swapped:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 (mk_i8 13) (mk_i8 12) (mk_i8 15) (mk_i8 14)
          (mk_i8 9) (mk_i8 8) (mk_i8 11) (mk_i8 10) (mk_i8 5) (mk_i8 4) (mk_i8 7) (mk_i8 6)
          (mk_i8 1) (mk_i8 0) (mk_i8 3) (mk_i8 2) (mk_i8 13) (mk_i8 12) (mk_i8 15) (mk_i8 14)
          (mk_i8 9) (mk_i8 8) (mk_i8 11) (mk_i8 10) (mk_i8 5) (mk_i8 4) (mk_i8 7) (mk_i8 6)
          (mk_i8 1) (mk_i8 0) (mk_i8 3) (mk_i8 2)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let products_right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 lhs rhs_adjacent_swapped
  in
  let products_right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s products_right
  in
  let products_right:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 (mk_i32 16) products_right
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 (mk_i32 170) products_left products_right

#pop-options
