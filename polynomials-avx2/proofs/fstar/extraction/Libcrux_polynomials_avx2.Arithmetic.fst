module Libcrux_polynomials_avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i16 = 20159s

let add (lhs rhs: u8) : u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_add_epi16 lhs rhs

let bitwise_and_with_constant (vector: u8) (constant: i16) : u8 =
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_and_si256 vector
    (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 constant <: u8)

let multiply_by_constant (vector: u8) (constant: i16) : u8 =
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 vector
    (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 constant <: u8)

let shift_left (v_SHIFT_BY: i32) (vector: u8) : u8 =
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_slli_epi16 v_SHIFT_BY vector

let shift_right (v_SHIFT_BY: i32) (vector: u8) : u8 =
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srai_epi16 v_SHIFT_BY vector

/// See Section 3.2 of the implementation notes document for an explanation
/// of this code.
let barrett_reduce (vector: u8) : u8 =
  let t:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 vector
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 v_BARRETT_MULTIPLIER <: u8)
  in
  let t:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_add_epi16 t
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 512s <: u8)
  in
  let quotient:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srai_epi16 10l t in
  let quotient_times_field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 quotient
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 Libcrux_traits.v_FIELD_MODULUS

        <:
        u8)
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 vector quotient_times_field_modulus

let cond_subtract_3329_ (vector: u8) : u8 =
  let field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 Libcrux_traits.v_FIELD_MODULUS
  in
  let vv_minus_field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 vector field_modulus
  in
  let sign_mask:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srai_epi16 15l vv_minus_field_modulus
  in
  let conditional_add_field_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_and_si256 sign_mask field_modulus
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_add_epi16 vv_minus_field_modulus
    conditional_add_field_modulus

let montgomery_multiply_by_constant (vector: u8) (constant: i16) : u8 =
  let constant:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 constant in
  let value_low:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 vector constant
  in
  let k:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 value_low
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 (cast (Libcrux_traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        u8)
  in
  let k_times_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 k
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 Libcrux_traits.v_FIELD_MODULUS

        <:
        u8)
  in
  let value_high:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 vector constant
  in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_by_constants (v c: u8) : u8 =
  let value_low:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 v c in
  let k:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 value_low
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 (cast (Libcrux_traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        u8)
  in
  let k_times_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 k
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi16 Libcrux_traits.v_FIELD_MODULUS

        <:
        u8)
  in
  let value_high:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 v c in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 value_high k_times_modulus

let montgomery_reduce_i32s (v: u8) : u8 =
  let k:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mullo_epi16 v
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi32 (cast (Libcrux_traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i32)
        <:
        u8)
  in
  let k_times_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_mulhi_epi16 k
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_set1_epi32 (cast (Libcrux_traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32)
        <:
        u8)
  in
  let value_high:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srli_epi32 16l v in
  let result:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 value_high k_times_modulus
  in
  let result:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_slli_epi32 16l result in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_srai_epi32 16l result

let sub (lhs rhs: u8) : u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm256_sub_epi16 lhs rhs

let montgomery_multiply_m128i_by_constants (v c: u8) : u8 =
  let value_low:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm_mullo_epi16 v c in
  let k:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_mullo_epi16 value_low
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set1_epi16 (cast (Libcrux_traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        u8)
  in
  let k_times_modulus:u8 =
    Libcrux_polynomials_avx2.Intrinsics_extraction.mm_mulhi_epi16 k
      (Libcrux_polynomials_avx2.Intrinsics_extraction.mm_set1_epi16 Libcrux_traits.v_FIELD_MODULUS
        <:
        u8)
  in
  let value_high:u8 = Libcrux_polynomials_avx2.Intrinsics_extraction.mm_mulhi_epi16 v c in
  Libcrux_polynomials_avx2.Intrinsics_extraction.mm_sub_epi16 value_high k_times_modulus
