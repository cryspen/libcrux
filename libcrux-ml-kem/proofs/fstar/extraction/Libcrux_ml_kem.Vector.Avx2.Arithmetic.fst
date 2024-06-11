module Libcrux_ml_kem.Vector.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add (lhs rhs: Core.Core_arch.X86.t____m256i) = Libcrux_intrinsics.Avx2.mm256_add_epi16 lhs rhs

let bitwise_and_with_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16) =
  Libcrux_intrinsics.Avx2.mm256_and_si256 vector
    (Libcrux_intrinsics.Avx2.mm256_set1_epi16 constant <: Core.Core_arch.X86.t____m256i)

let multiply_by_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16) =
  Libcrux_intrinsics.Avx2.mm256_mullo_epi16 vector
    (Libcrux_intrinsics.Avx2.mm256_set1_epi16 constant <: Core.Core_arch.X86.t____m256i)

let shift_right (v_SHIFT_BY: i32) (vector: Core.Core_arch.X86.t____m256i) =
  Libcrux_intrinsics.Avx2.mm256_srai_epi16 v_SHIFT_BY vector

let sub (lhs rhs: Core.Core_arch.X86.t____m256i) = Libcrux_intrinsics.Avx2.mm256_sub_epi16 lhs rhs

let barrett_reduce (vector: Core.Core_arch.X86.t____m256i) =
  let t:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 vector
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 v_BARRETT_MULTIPLIER
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let t:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi16 t
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 512s <: Core.Core_arch.X86.t____m256i)
  in
  let quotient:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_srai_epi16 10l t in
  let quotient_times_field_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 quotient
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Core.Core_arch.X86.t____m256i)
  in
  Libcrux_intrinsics.Avx2.mm256_sub_epi16 vector quotient_times_field_modulus

let cond_subtract_3329_ (vector: Core.Core_arch.X86.t____m256i) =
  let field_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
  in
  let vv_minus_field_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi16 vector field_modulus
  in
  let sign_mask:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi16 15l vv_minus_field_modulus
  in
  let conditional_add_field_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_and_si256 sign_mask field_modulus
  in
  Libcrux_intrinsics.Avx2.mm256_add_epi16 vv_minus_field_modulus conditional_add_field_modulus

let montgomery_multiply_by_constant (vector: Core.Core_arch.X86.t____m256i) (constant: i16) =
  let constant:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_set1_epi16 constant in
  let value_low:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 vector constant
  in
  let k:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let k_times_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let value_high:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 vector constant
  in
  Libcrux_intrinsics.Avx2.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_by_constants (v c: Core.Core_arch.X86.t____m256i) =
  let value_low:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_mullo_epi16 v c in
  let k:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let k_times_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2.mm256_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let value_high:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 v c in
  Libcrux_intrinsics.Avx2.mm256_sub_epi16 value_high k_times_modulus

let montgomery_multiply_m128i_by_constants (v c: Core.Core_arch.X86.t____m128i) =
  let value_low:Core.Core_arch.X86.t____m128i = Libcrux_intrinsics.Avx2.mm_mullo_epi16 v c in
  let k:Core.Core_arch.X86.t____m128i =
    Libcrux_intrinsics.Avx2.mm_mullo_epi16 value_low
      (Libcrux_intrinsics.Avx2.mm_set1_epi16 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i16)
        <:
        Core.Core_arch.X86.t____m128i)
  in
  let k_times_modulus:Core.Core_arch.X86.t____m128i =
    Libcrux_intrinsics.Avx2.mm_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2.mm_set1_epi16 Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
        <:
        Core.Core_arch.X86.t____m128i)
  in
  let value_high:Core.Core_arch.X86.t____m128i = Libcrux_intrinsics.Avx2.mm_mulhi_epi16 v c in
  Libcrux_intrinsics.Avx2.mm_sub_epi16 value_high k_times_modulus

let montgomery_reduce_i32s (v: Core.Core_arch.X86.t____m256i) =
  let k:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi16 v
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
                <:
                u32)
            <:
            i32)
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let k_times_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_mulhi_epi16 k
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS
                <:
                i16)
            <:
            i32)
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let value_high:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_srli_epi32 16l v in
  let result:Core.Core_arch.X86.t____m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi16 value_high k_times_modulus
  in
  let result:Core.Core_arch.X86.t____m256i = Libcrux_intrinsics.Avx2.mm256_slli_epi32 16l result in
  Libcrux_intrinsics.Avx2.mm256_srai_epi32 16l result
