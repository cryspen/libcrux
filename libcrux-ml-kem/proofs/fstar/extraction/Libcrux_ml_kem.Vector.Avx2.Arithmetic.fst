module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 lhs rhs

let bitwise_and_with_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  Libcrux_intrinsics.Avx2_extract.mm256_and_si256 vector
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let multiply_by_constant (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) (constant: i16) =
  Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector
    (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
      <:
      Libcrux_intrinsics.Avx2_extract.t_Vec256)

let shift_right (v_SHIFT_BY: i32) (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 v_SHIFT_BY vector

let sub (lhs rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 lhs rhs

let barrett_reduce (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 v_BARRETT_MULTIPLIER
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let t:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 t
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 512s
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let quotient:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 10l t
  in
  let quotient_times_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 quotient
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector quotient_times_field_modulus

let cond_subtract_3329_ (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let vv_minus_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 vector field_modulus
  in
  let sign_mask:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srai_epi16 15l vv_minus_field_modulus
  in
  let conditional_add_field_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_and_si256 sign_mask field_modulus
  in
  Libcrux_intrinsics.Avx2_extract.mm256_add_epi16 vv_minus_field_modulus
    conditional_add_field_modulus

let montgomery_multiply_by_constant
      (vector: Libcrux_intrinsics.Avx2_extract.t_Vec256)
      (constant: i16)
     =
  let constant:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 constant
  in
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 vector constant
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 vector constant
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 v c
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 v c
  in
  Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_m128i_by_constants (v c: Libcrux_intrinsics.Avx2_extract.t_Vec128) =
  let value_low:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mullo_epi16 v c
  in
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec128)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec128 =
    Libcrux_intrinsics.Avx2_extract.mm_mulhi_epi16 v c
  in
  Libcrux_intrinsics.Avx2_extract.mm_sub_epi16 value_high k_times_modulus

let montgomery_reduce_i32s (v: Libcrux_intrinsics.Avx2_extract.t_Vec256) =
  let k:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mullo_epi16 v
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let k_times_modulus:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2_extract.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32)
        <:
        Libcrux_intrinsics.Avx2_extract.t_Vec256)
  in
  let value_high:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_srli_epi32 16l v
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_sub_epi16 value_high k_times_modulus
  in
  let result:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
    Libcrux_intrinsics.Avx2_extract.mm256_slli_epi32 16l result
  in
  Libcrux_intrinsics.Avx2_extract.mm256_srai_epi32 16l result
