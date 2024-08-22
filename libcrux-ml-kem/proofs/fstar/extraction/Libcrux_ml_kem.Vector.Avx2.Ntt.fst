module Libcrux_ml_kem.Vector.Avx2.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inv_ntt_layer_1_step (vector: u8) (zeta0 zeta1 zeta2 zeta3: i16) =
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l vector in
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 160l vector in
  let rhs:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (-1s) (-1s) 1s 1s (-1s) (-1s) 1s 1s (-1s)
          (-1s) 1s 1s (-1s) (-1s) 1s 1s
        <:
        u8)
  in
  let sum:u8 = Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs in
  let sum_times_zetas:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants sum
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 zeta3 zeta3 0s 0s zeta2 zeta2 0s 0s zeta1
          zeta1 0s 0s zeta0 zeta0 0s 0s
        <:
        u8)
  in
  let sum:u8 = Libcrux_ml_kem.Vector.Avx2.Arithmetic.barrett_reduce sum in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 204l sum sum_times_zetas

let inv_ntt_layer_2_step (vector: u8) (zeta0 zeta1: i16) =
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 245l vector in
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 160l vector in
  let rhs:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (-1s) (-1s) (-1s) (-1s) 1s 1s 1s 1s (-1s)
          (-1s) (-1s) (-1s) 1s 1s 1s 1s
        <:
        u8)
  in
  let sum:u8 = Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs in
  let sum_times_zetas:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants sum
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 zeta1 zeta1 zeta1 zeta1 0s 0s 0s 0s zeta0
          zeta0 zeta0 zeta0 0s 0s 0s 0s
        <:
        u8)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 240l sum sum_times_zetas

let inv_ntt_layer_3_step (vector: u8) (zeta: i16) =
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l vector in
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector in
  let lower_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm_add_epi16 lhs rhs in
  let upper_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 lhs rhs in
  let upper_coefficients:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_m128i_by_constants upper_coefficients
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 zeta <: u8)
  in
  let combined:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients in
  Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 1l combined upper_coefficients

let ntt_layer_1_step (vector: u8) (zeta0 zeta1 zeta2 zeta3: i16) =
  let zetas:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (Core.Ops.Arith.Neg.neg zeta3 <: i16)
      (Core.Ops.Arith.Neg.neg zeta3 <: i16) zeta3 zeta3 (Core.Ops.Arith.Neg.neg zeta2 <: i16)
      (Core.Ops.Arith.Neg.neg zeta2 <: i16) zeta2 zeta2 (Core.Ops.Arith.Neg.neg zeta1 <: i16)
      (Core.Ops.Arith.Neg.neg zeta1 <: i16) zeta1 zeta1 (Core.Ops.Arith.Neg.neg zeta0 <: i16)
      (Core.Ops.Arith.Neg.neg zeta0 <: i16) zeta0 zeta0
  in
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 245l vector in
  let rhs:u8 = Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants rhs zetas in
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 160l vector in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let ntt_layer_2_step (vector: u8) (zeta0 zeta1: i16) =
  let zetas:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi16 (Core.Ops.Arith.Neg.neg zeta1 <: i16)
      (Core.Ops.Arith.Neg.neg zeta1 <: i16) (Core.Ops.Arith.Neg.neg zeta1 <: i16)
      (Core.Ops.Arith.Neg.neg zeta1 <: i16) zeta1 zeta1 zeta1 zeta1
      (Core.Ops.Arith.Neg.neg zeta0 <: i16) (Core.Ops.Arith.Neg.neg zeta0 <: i16)
      (Core.Ops.Arith.Neg.neg zeta0 <: i16) (Core.Ops.Arith.Neg.neg zeta0 <: i16) zeta0 zeta0 zeta0
      zeta0
  in
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 238l vector in
  let rhs:u8 = Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_by_constants rhs zetas in
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi32 68l vector in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let ntt_layer_3_step (vector: u8) (zeta: i16) =
  let rhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l vector in
  let rhs:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_multiply_m128i_by_constants rhs
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 zeta <: u8)
  in
  let lhs:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 vector in
  let lower_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm_add_epi16 lhs rhs in
  let upper_coefficients:u8 = Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 lhs rhs in
  let combined:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi128_si256 lower_coefficients in
  Libcrux_intrinsics.Avx2_extract.mm256_inserti128_si256 1l combined upper_coefficients

let ntt_multiply (lhs rhs: u8) (zeta0 zeta1 zeta2 zeta3: i16) =
  let shuffle_with:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 15y 14y 11y 10y 7y 6y 3y 2y 13y 12y 9y 8y 5y 4y
      1y 0y 15y 14y 11y 10y 7y 6y 3y 2y 13y 12y 9y 8y 5y 4y 1y 0y
  in
  let lhs_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 lhs shuffle_with in
  let lhs_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 216l lhs_shuffled in
  let lhs_evens:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 lhs_shuffled in
  let lhs_evens:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 lhs_evens in
  let lhs_odds:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l lhs_shuffled in
  let lhs_odds:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 lhs_odds in
  let rhs_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 rhs shuffle_with in
  let rhs_shuffled:u8 = Libcrux_intrinsics.Avx2_extract.mm256_permute4x64_epi64 216l rhs_shuffled in
  let rhs_evens:u8 = Libcrux_intrinsics.Avx2_extract.mm256_castsi256_si128 rhs_shuffled in
  let rhs_evens:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 rhs_evens in
  let rhs_odds:u8 = Libcrux_intrinsics.Avx2_extract.mm256_extracti128_si256 1l rhs_shuffled in
  let rhs_odds:u8 = Libcrux_intrinsics.Avx2_extract.mm256_cvtepi16_epi32 rhs_odds in
  let left:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 lhs_evens rhs_evens in
  let right:u8 = Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 lhs_odds rhs_odds in
  let right:u8 = Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s right in
  let right:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi32 right
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi32 (Core.Ops.Arith.Neg.neg (cast (zeta3 <: i16)
                <:
                i32)
            <:
            i32)
          (cast (zeta3 <: i16) <: i32)
          (Core.Ops.Arith.Neg.neg (cast (zeta2 <: i16) <: i32) <: i32)
          (cast (zeta2 <: i16) <: i32)
          (Core.Ops.Arith.Neg.neg (cast (zeta1 <: i16) <: i32) <: i32)
          (cast (zeta1 <: i16) <: i32)
          (Core.Ops.Arith.Neg.neg (cast (zeta0 <: i16) <: i32) <: i32)
          (cast (zeta0 <: i16) <: i32)
        <:
        u8)
  in
  let products_left:u8 = Libcrux_intrinsics.Avx2_extract.mm256_add_epi32 left right in
  let products_left:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s products_left
  in
  let rhs_adjacent_swapped:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_shuffle_epi8 rhs
      (Libcrux_intrinsics.Avx2_extract.mm256_set_epi8 13y 12y 15y 14y 9y 8y 11y 10y 5y 4y 7y 6y 1y
          0y 3y 2y 13y 12y 15y 14y 9y 8y 11y 10y 5y 4y 7y 6y 1y 0y 3y 2y
        <:
        u8)
  in
  let products_right:u8 =
    Libcrux_intrinsics.Avx2_extract.mm256_madd_epi16 lhs rhs_adjacent_swapped
  in
  let products_right:u8 =
    Libcrux_ml_kem.Vector.Avx2.Arithmetic.montgomery_reduce_i32s products_right
  in
  let products_right:u8 = Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 16l products_right in
  Libcrux_intrinsics.Avx2_extract.mm256_blend_epi16 170l products_left products_right
