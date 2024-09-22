/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
<<<<<<< HEAD
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: 7efec1624422fd5e94388ef06b9c76dfe7a48d46
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: e8928fc5424f83c8cb35b980033be17621fc0ef0
=======
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 97f7cefe14dabf275e4671ffea87e032d7779b71
>>>>>>> main
 */

#include "internal/libcrux_mlkem_avx2.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"
#include "internal/libcrux_sha3_avx2.h"

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input,
                                                          uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input,
                                                          uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

<<<<<<< HEAD
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_vec_zero(void) {
=======
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_zero(void) {
>>>>>>> main
  return mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ZERO_09(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array) {
=======
__m256i libcrux_ml_kem_vector_avx2_ZERO_ea(void) {
  return libcrux_ml_kem_vector_avx2_zero();
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array) {
>>>>>>> main
  return mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_from_i16_array_09(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_vec_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_vec_to_i16_array(
    __m256i v, int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, output, int16_t),
                         v);
  int16_t result[16U];
  memcpy(result, output, (size_t)16U * sizeof(int16_t));
  memcpy(ret, result, (size_t)16U * sizeof(int16_t));
=======
__m256i libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_i16_array(__m256i v,
                                                             int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, output, int16_t),
                         v);
  memcpy(ret, output, (size_t)16U * sizeof(int16_t));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_to_i16_array_09(__m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_vec_to_i16_array(x, ret);
=======
void libcrux_ml_kem_vector_avx2_to_i16_array_ea(__m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_to_i16_array(x, ret);
>>>>>>> main
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_add_09(__m256i lhs, __m256i *rhs) {
=======
__m256i libcrux_ml_kem_vector_avx2_add_ea(__m256i lhs, __m256i *rhs) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_sub_09(__m256i lhs, __m256i *rhs) {
=======
__m256i libcrux_ml_kem_vector_avx2_sub_ea(__m256i lhs, __m256i *rhs) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(__m256i vector,
                                                           int16_t constant) {
<<<<<<< HEAD
  __m256i cv = mm256_set1_epi16(constant);
  return mm256_mullo_epi16(vector, cv);
=======
  return mm256_mullo_epi16(vector, mm256_set1_epi16(constant));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_09(__m256i vec,
                                                           int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(vec, c);
=======
__m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(__m256i v,
                                                           int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(v, c);
>>>>>>> main
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant) {
<<<<<<< HEAD
  __m256i cv = mm256_set1_epi16(constant);
  return mm256_and_si256(vector, cv);
=======
  return mm256_and_si256(vector, mm256_set1_epi16(constant));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
=======
__m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
>>>>>>> main
    __m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vector, constant);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(__m256i vector) {
  __m256i field_modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i v_minus_field_modulus = mm256_sub_epi16(vector, field_modulus);
  __m256i sign_mask =
      mm256_srai_epi16((int32_t)15, v_minus_field_modulus, __m256i);
  __m256i conditional_add_field_modulus =
      mm256_and_si256(sign_mask, field_modulus);
  return mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_09(__m256i vector) {
=======
__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(__m256i vector) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i vector) {
<<<<<<< HEAD
  __m256i t0 = mm256_mulhi_epi16(
      vector, mm256_set1_epi16(
                  LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  __m256i t1 = mm256_add_epi16(t0, mm256_set1_epi16((int16_t)512));
  __m256i quotient = mm256_srai_epi16((int32_t)10, t1, __m256i);
=======
  __m256i t = mm256_mulhi_epi16(
      vector, mm256_set1_epi16(
                  LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  __m256i t0 = mm256_add_epi16(t, mm256_set1_epi16((int16_t)512));
  __m256i quotient = mm256_srai_epi16((int32_t)10, t0, __m256i);
>>>>>>> main
  __m256i quotient_times_field_modulus = mm256_mullo_epi16(
      quotient, mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return mm256_sub_epi16(vector, quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_barrett_reduce_09(__m256i vector) {
=======
__m256i libcrux_ml_kem_vector_avx2_barrett_reduce_ea(__m256i vector) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i vector, int16_t constant) {
<<<<<<< HEAD
  __m256i vec_constant = mm256_set1_epi16(constant);
  __m256i value_low = mm256_mullo_epi16(vector, vec_constant);
=======
  __m256i constant0 = mm256_set1_epi16(constant);
  __m256i value_low = mm256_mullo_epi16(vector, constant0);
>>>>>>> main
  __m256i k = mm256_mullo_epi16(
      value_low,
      mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
<<<<<<< HEAD
  __m256i modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus = mm256_mulhi_epi16(k, modulus);
  __m256i value_high = mm256_mulhi_epi16(vector, vec_constant);
=======
  __m256i k_times_modulus = mm256_mulhi_epi16(
      k, mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high = mm256_mulhi_epi16(vector, constant0);
>>>>>>> main
  return mm256_sub_epi16(value_high, k_times_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
=======
__m256i libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
>>>>>>> main
    __m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    __m256i vector) {
  __m256i field_modulus_halved = mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)2);
  __m256i field_modulus_quartered = mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)4);
  __m256i shifted = mm256_sub_epi16(field_modulus_halved, vector);
  __m256i mask = mm256_srai_epi16((int32_t)15, shifted, __m256i);
  __m256i shifted_to_positive = mm256_xor_si256(mask, shifted);
  __m256i shifted_to_positive_in_range =
      mm256_sub_epi16(shifted_to_positive, field_modulus_quartered);
  return mm256_srli_epi16((int32_t)15, shifted_to_positive_in_range, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_compress_1_09(__m256i vector) {
=======
__m256i libcrux_ml_kem_vector_avx2_compress_1_ea(__m256i vector) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(
    __m256i lhs, __m256i rhs) {
  __m256i prod02 = mm256_mul_epu32(lhs, rhs);
  __m256i prod13 =
      mm256_mul_epu32(mm256_shuffle_epi32((int32_t)245, lhs, __m256i),
                      mm256_shuffle_epi32((int32_t)245, rhs, __m256i));
  return mm256_unpackhi_epi64(mm256_unpacklo_epi32(prod02, prod13),
                              mm256_unpackhi_epi32(prod02, prod13));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
<<<<<<< HEAD
    __m256i vec, __m256i constants) {
  __m256i value_low = mm256_mullo_epi16(vec, constants);
=======
    __m256i v, __m256i c) {
  __m256i value_low = mm256_mullo_epi16(v, c);
>>>>>>> main
  __m256i k = mm256_mullo_epi16(
      value_low,
      mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
<<<<<<< HEAD
  __m256i modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus = mm256_mulhi_epi16(k, modulus);
  __m256i value_high = mm256_mulhi_epi16(vec, constants);
=======
  __m256i k_times_modulus = mm256_mulhi_epi16(
      k, mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high = mm256_mulhi_epi16(v, c);
>>>>>>> main
  return mm256_sub_epi16(value_high, k_times_modulus);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i zetas = mm256_set_epi16(-zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2,
                                  zeta2, zeta2, -zeta1, -zeta1, zeta1, zeta1,
                                  -zeta0, -zeta0, zeta0, zeta0);
  __m256i rhs = mm256_shuffle_epi32((int32_t)245, vector, __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs = mm256_shuffle_epi32((int32_t)160, vector, __m256i);
  return mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(__m256i vector,
>>>>>>> main
                                                       int16_t zeta0,
                                                       int16_t zeta1,
                                                       int16_t zeta2,
                                                       int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  __m256i zetas = mm256_set_epi16(-zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1,
                                  zeta1, zeta1, -zeta0, -zeta0, -zeta0, -zeta0,
                                  zeta0, zeta0, zeta0, zeta0);
  __m256i rhs = mm256_shuffle_epi32((int32_t)238, vector, __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs = mm256_shuffle_epi32((int32_t)68, vector, __m256i);
  return mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(__m256i vector,
>>>>>>> main
                                                       int16_t zeta0,
                                                       int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_MUSTINLINE __m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
<<<<<<< HEAD
    __m128i vec, __m128i constants) {
  __m128i value_low = mm_mullo_epi16(vec, constants);
=======
    __m128i v, __m128i c) {
  __m128i value_low = mm_mullo_epi16(v, c);
>>>>>>> main
  __m128i k = mm_mullo_epi16(
      value_low,
      mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
<<<<<<< HEAD
  __m128i modulus = mm_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m128i k_times_modulus = mm_mulhi_epi16(k, modulus);
  __m128i value_high = mm_mulhi_epi16(vec, constants);
=======
  __m128i k_times_modulus = mm_mulhi_epi16(
      k, mm_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m128i value_high = mm_mulhi_epi16(v, c);
>>>>>>> main
  return mm_sub_epi16(value_high, k_times_modulus);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(__m256i vector, int16_t zeta) {
  __m128i rhs = mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m128i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          rhs, mm_set1_epi16(zeta));
  __m128i lhs = mm256_castsi256_si128(vector);
  __m128i lower_coefficients = mm_add_epi16(lhs, rhs0);
  __m128i upper_coefficients = mm_sub_epi16(lhs, rhs0);
  __m256i combined = mm256_castsi128_si256(lower_coefficients);
  return mm256_inserti128_si256((int32_t)1, combined, upper_coefficients,
                                __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(__m256i vector,
>>>>>>> main
                                                       int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i lhs = mm256_shuffle_epi32((int32_t)245, vector, __m256i);
  __m256i rhs = mm256_shuffle_epi32((int32_t)160, vector, __m256i);
  __m256i rhs0 = mm256_mullo_epi16(
      rhs, mm256_set_epi16((int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                           (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                           (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                           (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1));
  __m256i sum0 = mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum0,
          mm256_set_epi16(zeta3, zeta3, (int16_t)0, (int16_t)0, zeta2, zeta2,
                          (int16_t)0, (int16_t)0, zeta1, zeta1, (int16_t)0,
                          (int16_t)0, zeta0, zeta0, (int16_t)0, (int16_t)0));
  __m256i sum = libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(sum0);
  return mm256_blend_epi16((int32_t)204, sum, sum_times_zetas, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(__m256i vector,
>>>>>>> main
                                                           int16_t zeta0,
                                                           int16_t zeta1,
                                                           int16_t zeta2,
                                                           int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  __m256i lhs = mm256_permute4x64_epi64((int32_t)245, vector, __m256i);
  __m256i rhs = mm256_permute4x64_epi64((int32_t)160, vector, __m256i);
  __m256i rhs0 = mm256_mullo_epi16(
      rhs, mm256_set_epi16((int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1,
                           (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1,
                           (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1,
                           (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1));
  __m256i sum = mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum,
          mm256_set_epi16(zeta1, zeta1, zeta1, zeta1, (int16_t)0, (int16_t)0,
                          (int16_t)0, (int16_t)0, zeta0, zeta0, zeta0, zeta0,
                          (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0));
  return mm256_blend_epi16((int32_t)240, sum, sum_times_zetas, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(__m256i vector,
>>>>>>> main
                                                           int16_t zeta0,
                                                           int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(
    __m256i vector, int16_t zeta) {
  __m128i lhs = mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m128i rhs = mm256_castsi256_si128(vector);
  __m128i lower_coefficients = mm_add_epi16(lhs, rhs);
  __m128i upper_coefficients = mm_sub_epi16(lhs, rhs);
  __m128i upper_coefficients0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          upper_coefficients, mm_set1_epi16(zeta));
  __m256i combined = mm256_castsi128_si256(lower_coefficients);
  return mm256_inserti128_si256((int32_t)1, combined, upper_coefficients0,
                                __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_09(__m256i vector,
=======
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(__m256i vector,
>>>>>>> main
                                                           int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE __m256i
<<<<<<< HEAD
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(__m256i vec) {
  __m256i k = mm256_mullo_epi16(
      vec,
=======
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(__m256i v) {
  __m256i k = mm256_mullo_epi16(
      v,
>>>>>>> main
      mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = mm256_mulhi_epi16(
      k, mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
<<<<<<< HEAD
  __m256i value_high = mm256_srli_epi32((int32_t)16, vec, __m256i);
=======
  __m256i value_high = mm256_srli_epi32((int32_t)16, v, __m256i);
>>>>>>> main
  __m256i result = mm256_sub_epi16(value_high, k_times_modulus);
  __m256i result0 = mm256_slli_epi32((int32_t)16, result, __m256i);
  return mm256_srai_epi32((int32_t)16, result0, __m256i);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(
    __m256i lhs, __m256i rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i shuffle_with = mm256_set_epi8(
      (int8_t)15, (int8_t)14, (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6,
      (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8,
      (int8_t)5, (int8_t)4, (int8_t)1, (int8_t)0, (int8_t)15, (int8_t)14,
      (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6, (int8_t)3, (int8_t)2,
      (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
      (int8_t)1, (int8_t)0);
  __m256i lhs_shuffled = mm256_shuffle_epi8(lhs, shuffle_with);
  __m256i lhs_shuffled0 =
      mm256_permute4x64_epi64((int32_t)216, lhs_shuffled, __m256i);
  __m128i lhs_evens = mm256_castsi256_si128(lhs_shuffled0);
  __m256i lhs_evens0 = mm256_cvtepi16_epi32(lhs_evens);
  __m128i lhs_odds =
      mm256_extracti128_si256((int32_t)1, lhs_shuffled0, __m128i);
  __m256i lhs_odds0 = mm256_cvtepi16_epi32(lhs_odds);
  __m256i rhs_shuffled = mm256_shuffle_epi8(rhs, shuffle_with);
  __m256i rhs_shuffled0 =
      mm256_permute4x64_epi64((int32_t)216, rhs_shuffled, __m256i);
  __m128i rhs_evens = mm256_castsi256_si128(rhs_shuffled0);
  __m256i rhs_evens0 = mm256_cvtepi16_epi32(rhs_evens);
  __m128i rhs_odds =
      mm256_extracti128_si256((int32_t)1, rhs_shuffled0, __m128i);
  __m256i rhs_odds0 = mm256_cvtepi16_epi32(rhs_odds);
  __m256i left = mm256_mullo_epi32(lhs_evens0, rhs_evens0);
  __m256i right = mm256_mullo_epi32(lhs_odds0, rhs_odds0);
  __m256i right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(right);
  __m256i right1 = mm256_mullo_epi32(
      right0, mm256_set_epi32(-(int32_t)zeta3, (int32_t)zeta3, -(int32_t)zeta2,
                              (int32_t)zeta2, -(int32_t)zeta1, (int32_t)zeta1,
                              -(int32_t)zeta0, (int32_t)zeta0));
  __m256i products_left = mm256_add_epi32(left, right1);
  __m256i products_left0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_left);
  __m256i rhs_adjacent_swapped = mm256_shuffle_epi8(
      rhs,
      mm256_set_epi8((int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14, (int8_t)9,
                     (int8_t)8, (int8_t)11, (int8_t)10, (int8_t)5, (int8_t)4,
                     (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0, (int8_t)3,
                     (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14,
                     (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10, (int8_t)5,
                     (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0,
                     (int8_t)3, (int8_t)2));
  __m256i products_right = mm256_madd_epi16(lhs, rhs_adjacent_swapped);
  __m256i products_right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_right);
  __m256i products_right1 =
      mm256_slli_epi32((int32_t)16, products_right0, __m256i);
  return mm256_blend_epi16((int32_t)170, products_left0, products_right1,
                           __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_ntt_multiply_09(__m256i *lhs, __m256i *rhs,
=======
__m256i libcrux_ml_kem_vector_avx2_ntt_multiply_ea(__m256i *lhs, __m256i *rhs,
>>>>>>> main
                                                   int16_t zeta0, int16_t zeta1,
                                                   int16_t zeta2,
                                                   int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    __m256i vector, uint8_t ret[2U]) {
  __m256i lsb_to_msb = mm256_slli_epi16((int32_t)15, vector, __m256i);
  __m128i low_msbs = mm256_castsi256_si128(lsb_to_msb);
  __m128i high_msbs = mm256_extracti128_si256((int32_t)1, lsb_to_msb, __m128i);
  __m128i msbs = mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = mm_movemask_epi8(msbs);
<<<<<<< HEAD
  ret[0U] = (uint8_t)bits_packed;
  ret[1U] = (uint8_t)(bits_packed >> 8U);
=======
  uint8_t serialized[2U] = {0U};
  serialized[0U] = (uint8_t)bits_packed;
  serialized[1U] = (uint8_t)(bits_packed >> 8U);
  memcpy(ret, serialized, (size_t)2U * sizeof(uint8_t));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_1_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_1_ea(__m256i vector,
>>>>>>> main
                                               uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  __m256i coefficients = mm256_set_epi16(
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  __m256i shift_lsb_to_msb = mm256_set_epi16(
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768,
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768);
  __m256i coefficients_in_msb =
      mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
  return mm256_srli_epi16((int32_t)15, coefficients_in_msb, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_1_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_1_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    __m256i vector, uint8_t ret[8U]) {
  uint8_t serialized[16U] = {0U};
  __m256i adjacent_2_combined = mm256_madd_epi16(
      vector, mm256_set_epi16(
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1));
  __m256i adjacent_8_combined = mm256_shuffle_epi8(
      adjacent_2_combined,
      mm256_set_epi8((int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4,
                     (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8,
                     (int8_t)4, (int8_t)0));
  __m256i combined = mm256_permutevar8x32_epi32(
      adjacent_8_combined,
      mm256_set_epi32((int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
                      (int32_t)0, (int32_t)0, (int32_t)4, (int32_t)0));
  __m128i combined0 = mm256_castsi256_si128(combined);
  mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t), combined0);
  uint8_t ret0[8U];
  core_result_Result_56 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)8U, uint8_t),
      Eurydice_slice, uint8_t[8U]);
<<<<<<< HEAD
  core_result_unwrap_41_0e(dst, ret0);
=======
  core_result_unwrap_26_0e(dst, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_4_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_4_ea(__m256i vector,
>>>>>>> main
                                               uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  __m256i coefficients = mm256_set_epi16(
      (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  __m256i shift_lsbs_to_msbs = mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  __m256i coefficients_in_msb =
      mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
  __m256i coefficients_in_lsb =
      mm256_srli_epi16((int32_t)4, coefficients_in_msb, __m256i);
  return mm256_and_si256(coefficients_in_lsb,
                         mm256_set1_epi16(((int16_t)1 << 4U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_4_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_4_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    __m256i vector, uint8_t ret[10U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = mm256_madd_epi16(
      vector, mm256_set_epi16(
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1));
  __m256i adjacent_4_combined = mm256_sllv_epi32(
      adjacent_2_combined,
      mm256_set_epi32((int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22,
                      (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22));
  __m256i adjacent_4_combined0 =
      mm256_srli_epi64((int32_t)22, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined =
      mm256_shuffle_epi32((int32_t)8, adjacent_4_combined0, __m256i);
  __m256i adjacent_8_combined0 = mm256_sllv_epi32(
      adjacent_8_combined,
      mm256_set_epi32((int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12,
                      (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12));
  __m256i adjacent_8_combined1 =
      mm256_srli_epi64((int32_t)12, adjacent_8_combined0, __m256i);
  __m128i lower_8 = mm256_castsi256_si128(adjacent_8_combined1);
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  __m128i upper_8 =
      mm256_extracti128_si256((int32_t)1, adjacent_8_combined1, __m128i);
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)5U, (size_t)21U, uint8_t),
      upper_8);
  uint8_t ret0[10U];
  core_result_Result_cd dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t),
      Eurydice_slice, uint8_t[10U]);
<<<<<<< HEAD
  core_result_unwrap_41_07(dst, ret0);
=======
  core_result_unwrap_26_07(dst, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_5_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_5_ea(__m256i vector,
>>>>>>> main
                                               uint8_t ret[10U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes) {
  __m128i coefficients =
      mm_set_epi8(Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
                  Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  __m256i coefficients_loaded = mm256_castsi128_si256(coefficients);
  __m256i coefficients_loaded0 = mm256_inserti128_si256(
      (int32_t)1, coefficients_loaded, coefficients, __m256i);
  __m256i coefficients0 = mm256_shuffle_epi8(
      coefficients_loaded0,
      mm256_set_epi8((int8_t)15, (int8_t)14, (int8_t)15, (int8_t)14, (int8_t)13,
                     (int8_t)12, (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10,
                     (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)9,
                     (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)7, (int8_t)6,
                     (int8_t)5, (int8_t)4, (int8_t)5, (int8_t)4, (int8_t)3,
                     (int8_t)2, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0,
                     (int8_t)1, (int8_t)0));
  __m256i coefficients1 = mm256_mullo_epi16(
      coefficients0,
      mm256_set_epi16((int16_t)1 << 0U, (int16_t)1 << 5U, (int16_t)1 << 2U,
                      (int16_t)1 << 7U, (int16_t)1 << 4U, (int16_t)1 << 9U,
                      (int16_t)1 << 6U, (int16_t)1 << 11U, (int16_t)1 << 0U,
                      (int16_t)1 << 5U, (int16_t)1 << 2U, (int16_t)1 << 7U,
                      (int16_t)1 << 4U, (int16_t)1 << 9U, (int16_t)1 << 6U,
                      (int16_t)1 << 11U));
  return mm256_srli_epi16((int32_t)11, coefficients1, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_5_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_5_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    __m256i vector, uint8_t ret[20U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = mm256_madd_epi16(
      vector, mm256_set_epi16((int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U,
                              (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
                              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U,
                              (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
                              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U,
                              (int16_t)1));
  __m256i adjacent_4_combined = mm256_sllv_epi32(
      adjacent_2_combined,
      mm256_set_epi32((int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12,
                      (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12));
  __m256i adjacent_4_combined0 =
      mm256_srli_epi64((int32_t)12, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = mm256_shuffle_epi8(
      adjacent_4_combined0,
      mm256_set_epi8((int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9,
                     (int8_t)8, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1,
                     (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10,
                     (int8_t)9, (int8_t)8, (int8_t)4, (int8_t)3, (int8_t)2,
                     (int8_t)1, (int8_t)0));
  __m128i lower_8 = mm256_castsi256_si128(adjacent_8_combined);
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  __m128i upper_8 =
      mm256_extracti128_si256((int32_t)1, adjacent_8_combined, __m128i);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice2(serialized, (size_t)10U,
                                                    (size_t)26U, uint8_t),
                        upper_8);
  uint8_t ret0[20U];
  core_result_Result_7a dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t),
      Eurydice_slice, uint8_t[20U]);
<<<<<<< HEAD
  core_result_unwrap_41_ea(dst, ret0);
=======
  core_result_unwrap_26_ea(dst, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_10_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_10_ea(__m256i vector,
>>>>>>> main
                                                uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes) {
  __m256i shift_lsbs_to_msbs = mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U);
  __m128i lower_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  __m128i lower_coefficients0 = mm_shuffle_epi8(
      lower_coefficients, mm_set_epi8(9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U, 4U, 3U,
                                      3U, 2U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)4U, (size_t)20U, uint8_t));
  __m128i upper_coefficients0 = mm_shuffle_epi8(
      upper_coefficients, mm_set_epi8(15U, 14U, 14U, 13U, 13U, 12U, 12U, 11U,
                                      10U, 9U, 9U, 8U, 8U, 7U, 7U, 6U));
  __m256i coefficients = mm256_castsi128_si256(lower_coefficients0);
  __m256i coefficients0 = mm256_inserti128_si256((int32_t)1, coefficients,
                                                 upper_coefficients0, __m256i);
  __m256i coefficients1 = mm256_mullo_epi16(coefficients0, shift_lsbs_to_msbs);
  __m256i coefficients2 = mm256_srli_epi16((int32_t)6, coefficients1, __m256i);
  return mm256_and_si256(coefficients2,
                         mm256_set1_epi16(((int16_t)1 << 10U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_10_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_10_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    __m256i vector, uint8_t ret[22U]) {
  int16_t array[16U] = {0U};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, array, int16_t),
                         vector);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable_from_i16_array_0d(
          Eurydice_array_to_slice((size_t)16U, array, int16_t));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_11_0d(input, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_11_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_11_ea(__m256i vector,
>>>>>>> main
                                                uint8_t ret[22U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_11_0d(bytes);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  return mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_11_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_11_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    __m256i vector, uint8_t ret[24U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = mm256_madd_epi16(
      vector, mm256_set_epi16((int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U,
                              (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
                              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U,
                              (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
                              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U,
                              (int16_t)1));
  __m256i adjacent_4_combined = mm256_sllv_epi32(
      adjacent_2_combined,
      mm256_set_epi32((int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8,
                      (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8));
  __m256i adjacent_4_combined0 =
      mm256_srli_epi64((int32_t)8, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = mm256_shuffle_epi8(
      adjacent_4_combined0,
      mm256_set_epi8((int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13,
                     (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
                     (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1,
                     (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                     (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9,
                     (int8_t)8, (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2,
                     (int8_t)1, (int8_t)0));
  __m128i lower_8 = mm256_castsi256_si128(adjacent_8_combined);
  __m128i upper_8 =
      mm256_extracti128_si256((int32_t)1, adjacent_8_combined, __m128i);
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice2(serialized, (size_t)12U,
                                                    (size_t)28U, uint8_t),
                        upper_8);
  uint8_t ret0[24U];
  core_result_Result_6f dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)24U, uint8_t),
      Eurydice_slice, uint8_t[24U]);
<<<<<<< HEAD
  core_result_unwrap_41_76(dst, ret0);
=======
  core_result_unwrap_26_76(dst, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
void libcrux_ml_kem_vector_avx2_serialize_12_09(__m256i vector,
=======
void libcrux_ml_kem_vector_avx2_serialize_12_ea(__m256i vector,
>>>>>>> main
                                                uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes) {
  __m256i shift_lsbs_to_msbs = mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  __m128i lower_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  __m128i lower_coefficients0 = mm_shuffle_epi8(
      lower_coefficients, mm_set_epi8(11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U, 5U, 4U,
                                      4U, 3U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)8U, (size_t)24U, uint8_t));
  __m128i upper_coefficients0 = mm_shuffle_epi8(
      upper_coefficients, mm_set_epi8(15U, 14U, 14U, 13U, 12U, 11U, 11U, 10U,
                                      9U, 8U, 8U, 7U, 6U, 5U, 5U, 4U));
  __m256i coefficients = mm256_castsi128_si256(lower_coefficients0);
  __m256i coefficients0 = mm256_inserti128_si256((int32_t)1, coefficients,
                                                 upper_coefficients0, __m256i);
  __m256i coefficients1 = mm256_mullo_epi16(coefficients0, shift_lsbs_to_msbs);
  __m256i coefficients2 = mm256_srli_epi16((int32_t)4, coefficients1, __m256i);
  return mm256_and_si256(coefficients2,
                         mm256_set1_epi16(((int16_t)1 << 12U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
<<<<<<< HEAD
__m256i libcrux_ml_kem_vector_avx2_deserialize_12_09(Eurydice_slice bytes) {
=======
__m256i libcrux_ml_kem_vector_avx2_deserialize_12_ea(Eurydice_slice bytes) {
>>>>>>> main
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output) {
  __m256i field_modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i potential_coefficients =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_12(input);
  __m256i compare_with_field_modulus =
      mm256_cmpgt_epi16(field_modulus, potential_coefficients);
  uint8_t good[2U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(compare_with_field_modulus,
                                                   good);
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[0U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients = mm256_castsi256_si128(potential_coefficients);
  __m128i lower_coefficients0 =
      mm_shuffle_epi8(lower_coefficients, lower_shuffles0);
  mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8_6__count_ones(good[0U]);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[1U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients =
      mm256_extracti128_si256((int32_t)1, potential_coefficients, __m128i);
  __m128i upper_coefficients0 =
      mm_shuffle_epi8(upper_coefficients, upper_shuffles0);
  mm_storeu_si128(Eurydice_slice_subslice2(output, sampled_count,
                                           sampled_count + (size_t)8U, int16_t),
                  upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8_6__count_ones(good[1U]);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
size_t libcrux_ml_kem_vector_avx2_rej_sample_09(Eurydice_slice input,
                                                Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
<<<<<<< HEAD
inline __m256i libcrux_ml_kem_vector_avx2_clone_78(__m256i *self) {
=======
inline __m256i libcrux_ml_kem_vector_avx2_clone_3a(__m256i *self) {
>>>>>>> main
  return self[0U];
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ZERO_20_1b(void) {
=======
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ZERO_d6_7d(void) {
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 lit;
  lit.coefficients[0U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[1U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[2U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[3U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[4U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[5U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[6U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[7U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[8U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[9U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[10U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[11U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[12U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[13U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[14U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  lit.coefficients[15U] = libcrux_ml_kem_vector_avx2_ZERO_09();
  return lit;
}

/**
 Only use with public values.

 This MUST NOT be used with secret inputs, like its caller
 `deserialize_ring_elements_reduced`.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_to_reduced_ring_element_55(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
=======
deserialize_to_reduced_ring_element_1b(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
<<<<<<< HEAD
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_09(bytes);
=======
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_ea(bytes);
>>>>>>> main
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_cond_subtract_3329_09(coefficient);
  }
  return re;
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_301(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c4(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
<<<<<<< HEAD
        deserialize_to_reduced_ring_element_55(ring_element);
=======
        deserialize_to_reduced_ring_element_1b(ring_element);
>>>>>>> main
    deserialized_pk[i0] = uu____0;
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1184
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_661(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_d6_7d(););
  deserialize_ring_elements_reduced_8c4(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
<<<<<<< HEAD
static KRML_MUSTINLINE __m256i shift_right_f5(__m256i vector) {
=======
static KRML_MUSTINLINE __m256i shift_right_84(__m256i vector) {
>>>>>>> main
  return mm256_srai_epi16((int32_t)15, vector, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.shift_right_09
with const generics
- SHIFT_BY= 15
*/
<<<<<<< HEAD
static __m256i shift_right_09_22(__m256i vector) {
  return shift_right_f5(vector);
=======
static __m256i shift_right_ea_fc(__m256i vector) {
  return shift_right_84(vector);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
<<<<<<< HEAD
static __m256i to_unsigned_representative_4f(__m256i a) {
  __m256i t = shift_right_09_22(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_09(a, &fm);
=======
static __m256i to_unsigned_representative_c0(__m256i a) {
  __m256i t = shift_right_ea_fc(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_ea(a, &fm);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_5c(
=======
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_53(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
<<<<<<< HEAD
    __m256i coefficient = to_unsigned_representative_4f(re->coefficients[i0]);
=======
    __m256i coefficient = to_unsigned_representative_c0(re->coefficients[i0]);
>>>>>>> main
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2_serialize_12_09(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)24U * i0, (size_t)24U * i0 + (size_t)24U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)24U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)384U * sizeof(uint8_t));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 1152
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_secret_key_501(
=======
static KRML_MUSTINLINE void serialize_secret_key_5f1(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[1152U]) {
  uint8_t out[1152U] = {0U};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret0[384U];
<<<<<<< HEAD
    serialize_uncompressed_ring_element_5c(&re, ret0);
=======
    serialize_uncompressed_ring_element_53(&re, ret0);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)1152U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_c21(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)1152U, uint8_t);
  uint8_t ret[1152U];
  serialize_secret_key_5f1(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1152U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1184U, serialized, (size_t)1152U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_public_key_511(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)1152U, uint8_t);
  uint8_t ret0[1152U];
  serialize_secret_key_501(t_as_ntt, ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1152U, ret0, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key_serialized,
                                      (size_t)1152U, uint8_t, size_t),
      seed_for_a, uint8_t);
  uint8_t result[1184U];
  memcpy(result, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)1184U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void serialize_public_key_021(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  serialize_public_key_mut_c21(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
>>>>>>> main
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
<<<<<<< HEAD
bool libcrux_ml_kem_ind_cca_validate_public_key_061(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  deserialize_ring_elements_reduced_301(
=======
bool libcrux_ml_kem_ind_cca_validate_public_key_051(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  deserialize_ring_elements_reduced_out_661(
>>>>>>> main
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
<<<<<<< HEAD
  serialize_public_key_511(
=======
  serialize_public_key_021(
>>>>>>> main
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 3
*/
static KRML_MUSTINLINE void H_a9_161(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_4d1(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  uint8_t t[32U];
  H_a9_161(Eurydice_array_to_subslice2(
               private_key->value, (size_t)384U * (size_t)3U,
               (size_t)768U * (size_t)3U + (size_t)32U, uint8_t),
           t);
  Eurydice_slice expected = Eurydice_array_to_subslice2(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t);
  return core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq(
      (size_t)32U, t, &expected, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
} IndCpaPrivateKeyUnpacked_a0;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_1a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static IndCpaPrivateKeyUnpacked_a0 default_1a_191(void) {
  IndCpaPrivateKeyUnpacked_a0 lit;
  lit.secret_as_ntt[0U] = ZERO_d6_7d();
  lit.secret_as_ntt[1U] = ZERO_d6_7d();
  lit.secret_as_ntt[2U] = ZERO_d6_7d();
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct IndCpaPublicKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
} IndCpaPublicKeyUnpacked_a0;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8d
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static IndCpaPublicKeyUnpacked_a0 default_8d_801(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  uu____0[i] = ZERO_d6_7d(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_d6_7d();
  lit.A[0U][1U] = ZERO_d6_7d();
  lit.A[0U][2U] = ZERO_d6_7d();
  lit.A[1U][0U] = ZERO_d6_7d();
  lit.A[1U][1U] = ZERO_d6_7d();
  lit.A[1U][2U] = ZERO_d6_7d();
  lit.A[2U][0U] = ZERO_d6_7d();
  lit.A[2U][1U] = ZERO_d6_7d();
  lit.A[2U][2U] = ZERO_d6_7d();
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void G_a9_ab1(Eurydice_slice input, uint8_t ret[64U]) {
=======
static KRML_MUSTINLINE void G_a9_671(Eurydice_slice input, uint8_t ret[64U]) {
>>>>>>> main
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
<<<<<<< HEAD
static void closure_ba1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void cpa_keygen_seed_d8_e11(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  uint8_t ret0[64U];
  G_a9_671(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_501(uint8_t input[3U][34U]) {
=======
shake128_init_absorb_2a1(uint8_t input[3U][34U]) {
>>>>>>> main
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t));
  return state;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_a9 with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_a9_3f1(uint8_t input[3U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[3U][34U];
  memcpy(copy_of_input, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_501(copy_of_input);
=======
shake128_init_absorb_a9_1c1(uint8_t input[3U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[3U][34U];
  memcpy(copy_of_input, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_2a1(copy_of_input);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_001(
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_0c1(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[3U][504U]) {
  uint8_t out[3U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t));
  uint8_t uu____0[504U];
  memcpy(uu____0, out0, (size_t)504U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____1[504U];
  memcpy(uu____1, out1, (size_t)504U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____2[504U];
  memcpy(uu____2, out2, (size_t)504U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)504U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_a9 with
const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_941(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_first_three_blocks_001(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_a9_2e1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_three_blocks_0c1(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 504
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_613(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_743(
>>>>>>> main
    uint8_t randomness[3U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block with const
generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_dd1(
=======
static KRML_MUSTINLINE void shake128_squeeze_block_4a1(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[3U][168U]) {
  uint8_t out[3U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  uint8_t uu____0[168U];
  memcpy(uu____0, out0, (size_t)168U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____1[168U];
  memcpy(uu____1, out1, (size_t)168U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____2[168U];
  memcpy(uu____2, out2, (size_t)168U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)168U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_a9 with const
generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_bf1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_next_block_dd1(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_block_a9_1d1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_block_4a1(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 168
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_614(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_744(
>>>>>>> main
    uint8_t randomness[3U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
from_i16_array_20_82(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
=======
from_i16_array_d6_14(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
<<<<<<< HEAD
        libcrux_ml_kem_vector_avx2_from_i16_array_09(Eurydice_slice_subslice2(
=======
        libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice_subslice2(
>>>>>>> main
            a, i0 * (size_t)16U, (i0 + (size_t)1U) * (size_t)16U, int16_t));
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
<<<<<<< HEAD
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_8a1(
    int16_t s[272U]) {
  return from_i16_array_20_82(
=======
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_e41(
    int16_t s[272U]) {
  return from_i16_array_d6_14(
>>>>>>> main
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_from_xof_c11(
=======
static KRML_MUSTINLINE void sample_from_xof_671(
>>>>>>> main
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[3U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
<<<<<<< HEAD
      shake128_init_absorb_final_a9_3f1(copy_of_seeds);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_first_three_blocks_a9_941(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[3U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_613(
=======
      shake128_init_absorb_a9_1c1(copy_of_seeds);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_three_blocks_a9_2e1(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[3U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_743(
>>>>>>> main
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
<<<<<<< HEAD
      shake128_squeeze_next_block_a9_bf1(&xof_state, randomness);
=======
      shake128_squeeze_block_a9_1d1(&xof_state, randomness);
>>>>>>> main
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[3U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)3U * sizeof(uint8_t[168U]));
<<<<<<< HEAD
      done = sample_from_uniform_distribution_next_614(
=======
      done = sample_from_uniform_distribution_next_744(
>>>>>>> main
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
<<<<<<< HEAD
                  ret0[i] = closure_8a1(copy_of_out[i]););
=======
                  ret0[i] = closure_e41(copy_of_out[i]););
>>>>>>> main
  memcpy(
      ret, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_matrix_A_ff1(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  closure_ba1(A_transpose[i]););
=======
static KRML_MUSTINLINE void sample_matrix_A_341(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[3U],
    uint8_t seed[34U], bool transpose) {
>>>>>>> main
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seed[34U];
      memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[3U][34U]; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seeds[3U][34U];
      memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[3U];
<<<<<<< HEAD
      sample_from_xof_c11(copy_of_seeds, sampled);
=======
      sample_from_xof_671(copy_of_seeds, sampled);
>>>>>>> main
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)3U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      }

  );
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U][3U];
  memcpy(result, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(ret, result,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
=======
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_ef2(uint8_t (*input)[33U],
=======
static KRML_MUSTINLINE void PRFxN_082(uint8_t (*input)[33U],
>>>>>>> main
                                      uint8_t ret[3U][128U]) {
  uint8_t out[3U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t));
  uint8_t uu____0[128U];
  memcpy(uu____0, out0, (size_t)128U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____1[128U];
  memcpy(uu____1, out1, (size_t)128U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____2[128U];
  memcpy(uu____2, out2, (size_t)128U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)128U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_a9
with const generics
- K= 3
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_a9_412(uint8_t (*input)[33U],
                                         uint8_t ret[3U][128U]) {
  PRFxN_ef2(input, ret);
=======
static KRML_MUSTINLINE void PRFxN_a9_162(uint8_t (*input)[33U],
                                         uint8_t ret[3U][128U]) {
  PRFxN_082(input, ret);
>>>>>>> main
}

/**
 Given a series of uniformly random bytes in `randomness`, for some number
 `eta`, the `sample_from_binomial_distribution_{eta}` functions sample a ring
 element from a binomial distribution centered at 0 that uses two sets of `eta`
 coin flips. If, for example, `eta = ETA`, each ring coefficient is a value `v`
 such such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:

 ```plaintext
 - If v < 0, Pr[v] = Pr[-v]
 - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
 ```

 The values `v < 0` are mapped to the appropriate `KyberFieldElement`.

 The expected value is:

 ```plaintext
 E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1]
 + (ETA)Pr[ETA] = 0 since Pr[-v] = Pr[v] when v < 0.
 ```

 And the variance is:

 ```plaintext
 Var(X) = E[(X - E[X])^2]
        = E[X^2]
        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) /
 2^(2 * ETA)) = ETA / 2
 ```

 This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203
 standard, which is reproduced below:

 ```plaintext
 Input: byte array B ∈ 𝔹^{64η}.
 Output: array f ∈ ℤ₂₅₆.

 b ← BytesToBits(B)
 for (i ← 0; i < 256; i++)
     x ← ∑(j=0 to η - 1) b[2iη + j]
     y ← ∑(j=0 to η - 1) b[2iη + η + j]
     f[i] ← x−y mod q
 end for
 return f
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
sample_from_binomial_distribution_2_6a(Eurydice_slice randomness) {
=======
sample_from_binomial_distribution_2_ea(Eurydice_slice randomness) {
>>>>>>> main
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice2(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t);
    uint32_t random_bits_as_u32 =
        (((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                         uint8_t *) |
          (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                         uint8_t *)
              << 8U) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                        uint8_t *)
             << 16U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U, uint8_t,
                                       uint8_t *)
            << 24U;
    uint32_t even_bits = random_bits_as_u32 & 1431655765U;
    uint32_t odd_bits = random_bits_as_u32 >> 1U & 1431655765U;
    uint32_t coin_toss_outcomes = even_bits + odd_bits;
    for (uint32_t i = 0U; i < CORE_NUM__U32_8__BITS / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      sampled_i16s[(size_t)8U * chunk_number + offset] = outcome_1 - outcome_2;
    }
  }
<<<<<<< HEAD
  return from_i16_array_20_82(
=======
  return from_i16_array_d6_14(
>>>>>>> main
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
sample_from_binomial_distribution_3_5f(Eurydice_slice randomness) {
=======
sample_from_binomial_distribution_3_3c(Eurydice_slice randomness) {
>>>>>>> main
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)3U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice2(
        randomness, chunk_number * (size_t)3U,
        chunk_number * (size_t)3U + (size_t)3U, uint8_t);
    uint32_t random_bits_as_u24 =
        ((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                        uint8_t *) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                        uint8_t *)
             << 8U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                       uint8_t *)
            << 16U;
    uint32_t first_bits = random_bits_as_u24 & 2396745U;
    uint32_t second_bits = random_bits_as_u24 >> 1U & 2396745U;
    uint32_t third_bits = random_bits_as_u24 >> 2U & 2396745U;
    uint32_t coin_toss_outcomes = first_bits + second_bits + third_bits;
    for (int32_t i = (int32_t)0; i < (int32_t)24 / (int32_t)6; i++) {
      int32_t outcome_set = i;
      int32_t outcome_set0 = outcome_set * (int32_t)6;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 7U);
      int16_t outcome_2 = (int16_t)(coin_toss_outcomes >>
                                        (uint32_t)(outcome_set0 + (int32_t)3) &
                                    7U);
      size_t offset = (size_t)(outcome_set0 / (int32_t)6);
      sampled_i16s[(size_t)4U * chunk_number + offset] = outcome_1 - outcome_2;
    }
  }
<<<<<<< HEAD
  return from_i16_array_20_82(
=======
  return from_i16_array_d6_14(
>>>>>>> main
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
sample_from_binomial_distribution_8e0(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_6a(randomness);
=======
sample_from_binomial_distribution_af(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_ea(randomness);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_at_layer_7_ea(
=======
static KRML_MUSTINLINE void ntt_at_layer_7_ab(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
<<<<<<< HEAD
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_09(
=======
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
>>>>>>> main
        re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_avx2_sub_09(re->coefficients[j], &t);
    re->coefficients[j] =
        libcrux_ml_kem_vector_avx2_add_09(re->coefficients[j], &t);
  }
}

typedef struct libcrux_ml_kem_vector_avx2_SIMD256Vector_x2_s {
  __m256i fst;
  __m256i snd;
} libcrux_ml_kem_vector_avx2_SIMD256Vector_x2;

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static __m256i montgomery_multiply_fe_25(__m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(v, fer);
=======
static __m256i montgomery_multiply_fe_aa(__m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(v, fer);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
<<<<<<< HEAD
ntt_layer_int_vec_step_0a(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i t = montgomery_multiply_fe_25(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_09(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_09(a, &t);
=======
ntt_layer_int_vec_step_c2(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i t = montgomery_multiply_fe_aa(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_ea(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_ea(a, &t);
>>>>>>> main
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_at_layer_4_plus_0d(
=======
static KRML_MUSTINLINE void ntt_at_layer_4_plus_b8(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t layer) {
  size_t step = (size_t)1U << (uint32_t)layer;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t offset = round * step * (size_t)2U;
    size_t offset_vec = offset / (size_t)16U;
    size_t step_vec = step / (size_t)16U;
    for (size_t i = offset_vec; i < offset_vec + step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_vector_avx2_SIMD256Vector_x2 uu____0 =
<<<<<<< HEAD
          ntt_layer_int_vec_step_0a(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]));
=======
          ntt_layer_int_vec_step_c2(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
>>>>>>> main
      __m256i x = uu____0.fst;
      __m256i y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_at_layer_3_db(
=======
static KRML_MUSTINLINE void ntt_at_layer_3_5f(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_09(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_at_layer_2_10(
=======
static KRML_MUSTINLINE void ntt_at_layer_2_c2(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_09(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_at_layer_1_6e(
=======
static KRML_MUSTINLINE void ntt_at_layer_1_60(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_1_step_09(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] + (size_t)1U),
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] + (size_t)2U),
          libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] + (size_t)3U));
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void poly_barrett_reduce_20_85(
=======
static KRML_MUSTINLINE void poly_barrett_reduce_d6_2b(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    self->coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_09(self->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_0d(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  ntt_at_layer_7_ea(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_db(&zeta_i, re);
  ntt_at_layer_2_10(&zeta_i, re);
  ntt_at_layer_1_6e(&zeta_i, re);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_d5(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  ntt_at_layer_7_ab(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_5f(&zeta_i, re);
  ntt_at_layer_2_c2(&zeta_i, re);
  ntt_at_layer_1_60(&zeta_i, re);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE tuple_b00 sample_vector_cbd_then_ntt_e41(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  re_as_ntt[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_ee1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[3U][128U];
<<<<<<< HEAD
  PRFxN_a9_412(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_8e0(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_0d(&re_as_ntt[i0]););
=======
  PRFxN_a9_162(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_af(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_d5(&re_as_ntt[i0]););
  return domain_separator;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[3size_t], uint8_t

*/
typedef struct tuple_b0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 fst[3U];
  uint8_t snd;
} tuple_b0;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt_out
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_b0 sample_vector_cbd_then_ntt_out_7f1(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  re_as_ntt[i] = ZERO_d6_7d(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_ee1(uu____0, uu____1, domain_separator);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[3U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
<<<<<<< HEAD
  tuple_b00 result;
  memcpy(
      result.fst, copy_of_re_as_ntt,
=======
  tuple_b0 lit;
  memcpy(
      lit.fst, copy_of_re_as_ntt,
>>>>>>> main
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
<<<<<<< HEAD
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_20
=======
 Given two `KyberPolynomialRingElement`s in their NTT representations,
 compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
 the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:

 ```plaintext
 ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X²
 - ζ^(2·BitRev₇(i) + 1))
 ```

 This function almost implements <strong>Algorithm 10</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
 Output: An array ĥ ∈ ℤq.

 for(i ← 0; i < 128; i++)
     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1],
 ζ^(2·BitRev₇(i) + 1)) end for return ĥ
 ```
 We say "almost" because the coefficients of the ring element output by
 this function are in the Montgomery domain.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
ntt_multiply_20_f1(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out = ZERO_20_1b();
=======
ntt_multiply_d6_f1(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    out.coefficients[i0] = libcrux_ml_kem_vector_avx2_ntt_multiply_09(
        &self->coefficients[i0], &rhs->coefficients[i0],
        libcrux_ml_kem_polynomial_get_zeta((size_t)64U + (size_t)4U * i0),
        libcrux_ml_kem_polynomial_get_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)1U),
        libcrux_ml_kem_polynomial_get_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)2U),
        libcrux_ml_kem_polynomial_get_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)3U));
  }
  return out;
}

/**
<<<<<<< HEAD
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_20
=======
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void add_to_ring_element_20_471(
=======
static KRML_MUSTINLINE void add_to_ring_element_d6_b81(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, self->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_09(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static __m256i to_standard_domain_f5(__m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
=======
static __m256i to_standard_domain_bd(__m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
>>>>>>> main
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void add_standard_error_reduce_20_f6(
=======
static KRML_MUSTINLINE void add_standard_error_reduce_d6_a7(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
<<<<<<< HEAD
        to_standard_domain_f5(self->coefficients[j]);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form,
=======
        to_standard_domain_bd(self->coefficients[j]);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form,
>>>>>>> main
                                          &error->coefficients[j]));
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_As_plus_e_ef1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result0[i] = ZERO_20_1b(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_20_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_20_471(&result0[i1], &product);
    }
    add_standard_error_reduce_20_f6(&result0[i1], &error_as_ntt[i1]);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  memcpy(
      result, result0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
=======
static KRML_MUSTINLINE void compute_As_plus_e_a21(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_d6_7d();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_d6_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_b81(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_a7(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
>>>>>>> main
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static tuple_9b0 generate_keypair_unpacked_471(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_ab1(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
=======
static void generate_keypair_unpacked_811(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_a0 *private_key,
    IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_e11(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
>>>>>>> main
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_171(seed_for_A0, ret);
  sample_matrix_A_ff1(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(seed_for_secret_and_error,
                                             prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____2 = sample_vector_cbd_then_ntt_e41(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
=======
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_341(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_ee1(uu____2, copy_of_prf_input0, 0U);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
<<<<<<< HEAD
      sample_vector_cbd_then_ntt_e41(copy_of_prf_input, domain_separator).fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  compute_As_plus_e_ef1(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[3U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A_transpose[3U]
                                                                        [3U];
  memcpy(copy_of_A_transpose, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 pk;
  memcpy(
      pk.t_as_ntt, copy_of_t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, copy_of_seed_for_A, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, copy_of_A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[3U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 sk;
  memcpy(
      sk.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_9b0){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void closure_1c1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_3a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2 clone_3a_33(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 lit;
  __m256i ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret, __m256i, void *);
  memcpy(lit.coefficients, ret, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 3
*/
static KRML_MUSTINLINE void H_a9_311(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_451(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  tuple_9b0 uu____0 = generate_keypair_unpacked_471(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, closure_1c1(A[i]););
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_3a_33(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[3U][3U];
  memcpy(uu____2, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t pk_serialized[1184U];
  serialize_public_key_511(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_311(Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U]);
  core_result_unwrap_41_33(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 uu____3 =
      ind_cpa_private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_implicit_rejection_value[32U];
  memcpy(copy_of_implicit_rejection_value, implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, copy_of_implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 uu____6 =
      ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_hash[32U];
  memcpy(copy_of_public_key_hash, public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, copy_of_public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  return lit;
=======
      sample_vector_cbd_then_ntt_out_7f1(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_a21(public_key->t_as_ntt, public_key->A,
                        private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static libcrux_ml_kem_utils_extraction_helper_Keypair768 generate_keypair_931(
    Eurydice_slice key_generation_seed) {
  tuple_9b0 uu____0 = generate_keypair_unpacked_471(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 pk = uu____0.snd;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_511(
      pk.t_as_ntt, Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key_501(sk.secret_as_ntt, secret_key_serialized);
=======
static libcrux_ml_kem_utils_extraction_helper_Keypair768 generate_keypair_2f1(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_a0 private_key = default_1a_191();
  IndCpaPublicKeyUnpacked_a0 public_key = default_8d_801();
  generate_keypair_unpacked_811(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1184U];
  serialize_public_key_021(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key_5f1(private_key.secret_as_ntt, secret_key_serialized);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1152U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1184U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
<<<<<<< HEAD
  libcrux_ml_kem_utils_extraction_helper_Keypair768 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  return result;
=======
  libcrux_ml_kem_utils_extraction_helper_Keypair768 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_kem_secret_key_eb1(
=======
static KRML_MUSTINLINE void serialize_kem_secret_key_0a1(
>>>>>>> main
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t);
  uint8_t ret0[32U];
<<<<<<< HEAD
  H_a9_311(public_key, ret0);
=======
  H_a9_161(public_key, ret0);
>>>>>>> main
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
  memcpy(ret, out, (size_t)2400U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
<<<<<<< HEAD
libcrux_ml_kem_ind_cca_generate_keypair_f71(uint8_t randomness[64U]) {
=======
libcrux_ml_kem_ind_cca_generate_keypair_511(uint8_t randomness[64U]) {
>>>>>>> main
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
<<<<<<< HEAD
      generate_keypair_931(ind_cpa_keypair_randomness);
=======
      generate_keypair_2f1(ind_cpa_keypair_randomness);
>>>>>>> main
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
<<<<<<< HEAD
  serialize_kem_secret_key_eb1(
=======
  serialize_kem_secret_key_0a1(
>>>>>>> main
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
<<<<<<< HEAD
      libcrux_ml_kem_types_from_e7_f10(copy_of_secret_key_serialized);
=======
      libcrux_ml_kem_types_from_88_2d0(copy_of_secret_key_serialized);
>>>>>>> main
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
<<<<<<< HEAD
  return libcrux_ml_kem_types_from_64_b10(
      uu____2, libcrux_ml_kem_types_from_07_a90(copy_of_public_key));
=======
  return libcrux_ml_kem_types_from_17_8b0(
      uu____2, libcrux_ml_kem_types_from_40_600(copy_of_public_key));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_d8_961(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1152
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c1(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_1b(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE tuple_b00
sample_ring_element_cbd_e71(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE tuple_b0
sample_ring_element_cbd_c61(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_d6_7d(););
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[3U][128U];
<<<<<<< HEAD
  PRFxN_a9_412(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_8e0(
=======
  PRFxN_a9_162(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_af(
>>>>>>> main
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[3U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
<<<<<<< HEAD
  tuple_b00 result;
  memcpy(
      result.fst, copy_of_error_1,
=======
  tuple_b0 lit;
  memcpy(
      lit.fst, copy_of_error_1,
>>>>>>> main
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_c90(Eurydice_slice input, uint8_t ret[128U]) {
=======
static KRML_MUSTINLINE void PRF_d10(Eurydice_slice input, uint8_t ret[128U]) {
>>>>>>> main
  uint8_t digest[128U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)128U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 3
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_264(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_c90(input, ret);
=======
static KRML_MUSTINLINE void PRF_a9_424(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_d10(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_at_layer_1_16(
=======
static KRML_MUSTINLINE void invert_ntt_at_layer_1_2b(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_09(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] - (size_t)1U),
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] - (size_t)2U),
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] - (size_t)3U));
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_at_layer_2_88(
=======
static KRML_MUSTINLINE void invert_ntt_at_layer_2_6a(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_09(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_at_layer_3_f7(
=======
static KRML_MUSTINLINE void invert_ntt_at_layer_3_ad(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] - (size_t)1U;
                   re->coefficients[round] =
                       libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_09(
                           re->coefficients[round],
                           libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
<<<<<<< HEAD
inv_ntt_layer_int_vec_step_reduce_e0(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_09(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
      libcrux_ml_kem_vector_avx2_add_09(a, &b));
  b = montgomery_multiply_fe_25(a_minus_b, zeta_r);
=======
inv_ntt_layer_int_vec_step_reduce_63(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_ea(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
      libcrux_ml_kem_vector_avx2_add_ea(a, &b));
  b = montgomery_multiply_fe_aa(a_minus_b, zeta_r);
>>>>>>> main
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_84(
=======
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_8f(
>>>>>>> main
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t layer) {
  size_t step = (size_t)1U << (uint32_t)layer;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    size_t offset = round * step * (size_t)2U;
    size_t offset_vec =
        offset / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
    size_t step_vec =
        step / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
    for (size_t i = offset_vec; i < offset_vec + step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_vector_avx2_SIMD256Vector_x2 uu____0 =
<<<<<<< HEAD
          inv_ntt_layer_int_vec_step_reduce_e0(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]));
=======
          inv_ntt_layer_int_vec_step_reduce_63(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
>>>>>>> main
      __m256i x = uu____0.fst;
      __m256i y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_montgomery_971(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_16(&zeta_i, re);
  invert_ntt_at_layer_2_88(&zeta_i, re);
  invert_ntt_at_layer_3_f7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void invert_ntt_montgomery_191(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_2b(&zeta_i, re);
  invert_ntt_at_layer_2_6a(&zeta_i, re);
  invert_ntt_at_layer_3_ad(&zeta_i, re);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void add_error_reduce_20_1f(
=======
static KRML_MUSTINLINE void add_error_reduce_d6_89(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
<<<<<<< HEAD
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
=======
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
>>>>>>> main
            self->coefficients[j], (int16_t)1441);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_vector_u_e31(
=======
static KRML_MUSTINLINE void compute_vector_u_ba1(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
<<<<<<< HEAD
                  result0[i] = ZERO_20_1b(););
=======
                  result[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
<<<<<<< HEAD
          ntt_multiply_20_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_20_471(&result0[i1], &product);
    }
    invert_ntt_montgomery_971(&result0[i1]);
    add_error_reduce_20_1f(&result0[i1], &error_1[i1]);
=======
          ntt_multiply_d6_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_b81(&result[i1], &product);
    }
    invert_ntt_montgomery_191(&result[i1]);
    add_error_reduce_d6_89(&result[i1], &error_1[i1]);
>>>>>>> main
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  memcpy(
      result, result0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static __m256i decompress_1_34(__m256i vec) {
  __m256i z = libcrux_ml_kem_vector_avx2_ZERO_09();
  __m256i s = libcrux_ml_kem_vector_avx2_sub_09(z, &vec);
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(s,
                                                                 (int16_t)1665);
=======
static __m256i decompress_1_f2(__m256i v) {
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
      libcrux_ml_kem_vector_avx2_sub_ea(libcrux_ml_kem_vector_avx2_ZERO_ea(),
                                        &v),
      (int16_t)1665);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_message_e3(uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_deserialize_1_09(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t));
      re.coefficients[i0] = decompress_1_34(coefficient_compressed););
=======
deserialize_then_decompress_message_ef(uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_deserialize_1_ea(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t));
      re.coefficients[i0] = decompress_1_f2(coefficient_compressed););
>>>>>>> main
  return re;
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
add_message_error_reduce_20_69(
=======
add_message_error_reduce_d6_df(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
<<<<<<< HEAD
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
            result.coefficients[i0], (int16_t)1441);
    __m256i tmp = libcrux_ml_kem_vector_avx2_add_09(self->coefficients[i0],
                                                    &message->coefficients[i0]);
    __m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form, &tmp);
=======
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            result.coefficients[i0], (int16_t)1441);
    __m256i tmp = libcrux_ml_kem_vector_avx2_add_ea(self->coefficients[i0],
                                                    &message->coefficients[i0]);
    __m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form, &tmp);
>>>>>>> main
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_09(tmp0);
  }
  return result;
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_ring_element_v_e71(
=======
compute_ring_element_v_9f1(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_20_471(&result, &product););
  invert_ntt_montgomery_971(&result);
  result = add_message_error_reduce_20_69(error_2, message, result);
=======
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_b81(&result, &product););
  invert_ntt_montgomery_191(&result);
  result = add_message_error_reduce_d6_df(error_2, message, result);
>>>>>>> main
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
compress_ciphertext_coefficient_fd(__m256i vector) {
=======
compress_ciphertext_coefficient_43(__m256i vector) {
>>>>>>> main
  __m256i field_modulus_halved = mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor = mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask =
      mm256_set1_epi32(((int32_t)1 << (uint32_t)(int32_t)10) - (int32_t)1);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low =
      mm256_slli_epi32((int32_t)10, coefficients_low0, __m256i);
  __m256i compressed_low0 =
      mm256_add_epi32(compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 =
      mm256_srli_epi32((int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 =
      mm256_and_si256(compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high =
      mm256_slli_epi32((int32_t)10, coefficients_high0, __m256i);
  __m256i compressed_high0 =
      mm256_add_epi32(compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 =
      mm256_srli_epi32((int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 =
      mm256_and_si256(compressed_high2, coefficient_bits_mask);
  __m256i compressed = mm256_packs_epi32(compressed_low3, compressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_09
with const generics
- COEFFICIENT_BITS= 10
*/
<<<<<<< HEAD
static __m256i compress_09_76(__m256i vector) {
  return compress_ciphertext_coefficient_fd(vector);
=======
static __m256i compress_ea_ab(__m256i vector) {
  return compress_ciphertext_coefficient_43(vector);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_10_bf(
=======
static KRML_MUSTINLINE void compress_then_serialize_10_190(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
<<<<<<< HEAD
        compress_09_76(to_unsigned_representative_4f(re->coefficients[i0]));
=======
        compress_ea_ab(to_unsigned_representative_c0(re->coefficients[i0]));
>>>>>>> main
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2_serialize_10_09(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)20U * i0, (size_t)20U * i0 + (size_t)20U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)20U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
compress_ciphertext_coefficient_fd0(__m256i vector) {
=======
compress_ciphertext_coefficient_430(__m256i vector) {
>>>>>>> main
  __m256i field_modulus_halved = mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor = mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask =
      mm256_set1_epi32(((int32_t)1 << (uint32_t)(int32_t)11) - (int32_t)1);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low =
      mm256_slli_epi32((int32_t)11, coefficients_low0, __m256i);
  __m256i compressed_low0 =
      mm256_add_epi32(compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 =
      mm256_srli_epi32((int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 =
      mm256_and_si256(compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high =
      mm256_slli_epi32((int32_t)11, coefficients_high0, __m256i);
  __m256i compressed_high0 =
      mm256_add_epi32(compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 =
      mm256_srli_epi32((int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 =
      mm256_and_si256(compressed_high2, coefficient_bits_mask);
  __m256i compressed = mm256_packs_epi32(compressed_low3, compressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_09
with const generics
- COEFFICIENT_BITS= 11
*/
<<<<<<< HEAD
static __m256i compress_09_760(__m256i vector) {
  return compress_ciphertext_coefficient_fd0(vector);
=======
static __m256i compress_ea_ab0(__m256i vector) {
  return compress_ciphertext_coefficient_430(vector);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_81(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_bf(re, uu____0);
=======
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_880(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_190(re, uu____0);
>>>>>>> main
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
<<<<<<< HEAD
static void compress_then_serialize_u_9f1(
=======
static void compress_then_serialize_u_0b1(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t);
    uint8_t ret[320U];
<<<<<<< HEAD
    compress_then_serialize_ring_element_u_81(&re, ret);
=======
    compress_then_serialize_ring_element_u_880(&re, ret);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
compress_ciphertext_coefficient_fd1(__m256i vector) {
=======
compress_ciphertext_coefficient_431(__m256i vector) {
>>>>>>> main
  __m256i field_modulus_halved = mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor = mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask =
      mm256_set1_epi32(((int32_t)1 << (uint32_t)(int32_t)4) - (int32_t)1);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low =
      mm256_slli_epi32((int32_t)4, coefficients_low0, __m256i);
  __m256i compressed_low0 =
      mm256_add_epi32(compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 =
      mm256_srli_epi32((int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 =
      mm256_and_si256(compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high =
      mm256_slli_epi32((int32_t)4, coefficients_high0, __m256i);
  __m256i compressed_high0 =
      mm256_add_epi32(compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 =
      mm256_srli_epi32((int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 =
      mm256_and_si256(compressed_high2, coefficient_bits_mask);
  __m256i compressed = mm256_packs_epi32(compressed_low3, compressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_09
with const generics
- COEFFICIENT_BITS= 4
*/
<<<<<<< HEAD
static __m256i compress_09_761(__m256i vector) {
  return compress_ciphertext_coefficient_fd1(vector);
=======
static __m256i compress_ea_ab1(__m256i vector) {
  return compress_ciphertext_coefficient_431(vector);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_4_c0(
=======
static KRML_MUSTINLINE void compress_then_serialize_4_f5(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  LowStar_Ignore_ignore(Eurydice_slice_len(serialized, uint8_t), size_t,
                        void *);
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
<<<<<<< HEAD
        compress_09_761(to_unsigned_representative_4f(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_09(coefficient, bytes);
=======
        compress_ea_ab1(to_unsigned_representative_c0(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_ea(coefficient, bytes);
>>>>>>> main
    Eurydice_slice_copy(
        Eurydice_slice_subslice2(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
compress_ciphertext_coefficient_fd2(__m256i vector) {
=======
compress_ciphertext_coefficient_432(__m256i vector) {
>>>>>>> main
  __m256i field_modulus_halved = mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor = mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask =
      mm256_set1_epi32(((int32_t)1 << (uint32_t)(int32_t)5) - (int32_t)1);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low =
      mm256_slli_epi32((int32_t)5, coefficients_low0, __m256i);
  __m256i compressed_low0 =
      mm256_add_epi32(compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 =
      mm256_srli_epi32((int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 =
      mm256_and_si256(compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high =
      mm256_slli_epi32((int32_t)5, coefficients_high0, __m256i);
  __m256i compressed_high0 =
      mm256_add_epi32(compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 =
      mm256_srli_epi32((int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 =
      mm256_and_si256(compressed_high2, coefficient_bits_mask);
  __m256i compressed = mm256_packs_epi32(compressed_low3, compressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_09
with const generics
- COEFFICIENT_BITS= 5
*/
<<<<<<< HEAD
static __m256i compress_09_762(__m256i vector) {
  return compress_ciphertext_coefficient_fd2(vector);
=======
static __m256i compress_ea_ab2(__m256i vector) {
  return compress_ciphertext_coefficient_432(vector);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_5_2c(
=======
static KRML_MUSTINLINE void compress_then_serialize_5_a4(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  LowStar_Ignore_ignore(Eurydice_slice_len(serialized, uint8_t), size_t,
                        void *);
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficients =
<<<<<<< HEAD
        compress_09_762(to_unsigned_representative_4f(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_09(coefficients, bytes);
=======
        compress_ea_ab2(to_unsigned_representative_c0(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_ea(coefficients, bytes);
>>>>>>> main
    Eurydice_slice_copy(
        Eurydice_slice_subslice2(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t),
        Eurydice_array_to_slice((size_t)10U, bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_0c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_4_c0(re, out);
=======
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_f30(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_4_f5(re, out);
>>>>>>> main
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_unpacked_061(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____1 = sample_vector_cbd_then_ntt_e41(copy_of_prf_input0, 0U);
=======
static void encrypt_unpacked_be1(IndCpaPublicKeyUnpacked_a0 *public_key,
                                 uint8_t message[32U],
                                 Eurydice_slice randomness,
                                 uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b0 uu____1 = sample_vector_cbd_then_ntt_out_7f1(copy_of_prf_input0, 0U);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
<<<<<<< HEAD
  tuple_b00 uu____3 =
      sample_ring_element_cbd_e71(copy_of_prf_input, domain_separator0);
=======
  tuple_b0 uu____3 =
      sample_ring_element_cbd_c61(copy_of_prf_input, domain_separator0);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
<<<<<<< HEAD
  PRF_a9_264(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_8e0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  compute_vector_u_e31(public_key->A, r_as_ntt, error_1, u);
=======
  PRF_a9_424(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_af(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  compute_vector_u_ba1(public_key->A, r_as_ntt, error_1, u);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
<<<<<<< HEAD
      deserialize_then_decompress_message_e3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_e71(public_key->t_as_ntt, r_as_ntt, &error_2,
=======
      deserialize_then_decompress_message_ef(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_9f1(public_key->t_as_ntt, r_as_ntt, &error_2,
>>>>>>> main
                                 &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
<<<<<<< HEAD
  compress_then_serialize_u_9f1(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_0c(
=======
  compress_then_serialize_u_0b1(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_f30(
>>>>>>> main
      uu____6, Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                               (size_t)960U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
<<<<<<< HEAD
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_3c libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_251(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  Eurydice_slice_copy(uu____0,
                      Eurydice_array_to_slice(
                          (size_t)32U, public_key->public_key_hash, uint8_t),
                      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab1(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____2 =
      &public_key->ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_unpacked_061(uu____2, copy_of_randomness, pseudorandomness,
                       ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types_from_15_e90(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_3c lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.entropy_preprocess_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_af_151(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, randomness, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
}

/**
=======
>>>>>>> main
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_501(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1088U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  deserialize_ring_elements_reduced_301(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t),
      t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_171(seed, ret0);
  sample_matrix_A_ff1(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[3U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A[3U][3U];
  memcpy(copy_of_A, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, copy_of_t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, copy_of_seed_for_A,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, copy_of_A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &public_key_unpacked;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[1088U];
  encrypt_unpacked_061(uu____3, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)1088U * sizeof(uint8_t));
=======
static void encrypt_a41(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1088U]) {
  IndCpaPublicKeyUnpacked_a0 unpacked_public_key = default_8d_801();
  deserialize_ring_elements_reduced_8c1(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[3U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_341(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_a0 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1088U];
  encrypt_unpacked_be1(uu____1, copy_of_message, randomness, ret1);
  memcpy(ret, ret1, (size_t)1088U * sizeof(uint8_t));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void kdf_af_6e1(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, shared_secret, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
=======
static KRML_MUSTINLINE void kdf_d8_e91(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_b31(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_151(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_9c1(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_961(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
<<<<<<< HEAD
  H_a9_311(Eurydice_array_to_slice(
               (size_t)1184U, libcrux_ml_kem_types_as_slice_f6_ae0(public_key),
=======
  H_a9_161(Eurydice_array_to_slice(
               (size_t)1184U, libcrux_ml_kem_types_as_slice_ba_121(public_key),
>>>>>>> main
               uint8_t),
           ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
<<<<<<< HEAD
  G_a9_ab1(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
=======
  G_a9_671(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
<<<<<<< HEAD
      (size_t)1184U, libcrux_ml_kem_types_as_slice_f6_ae0(public_key), uint8_t);
=======
      (size_t)1184U, libcrux_ml_kem_types_as_slice_ba_121(public_key), uint8_t);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
<<<<<<< HEAD
  encrypt_501(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
=======
  encrypt_a41(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
<<<<<<< HEAD
      libcrux_ml_kem_types_from_15_e90(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_af_6e1(shared_secret, shared_secret_array);
=======
      libcrux_ml_kem_types_from_fc_361(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_e91(shared_secret, shared_secret_array);
>>>>>>> main
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
<<<<<<< HEAD
  tuple_3c result;
  result.fst = uu____5;
  memcpy(result.snd, copy_of_shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  return result;
=======
  tuple_3c lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_uncompressed_ring_element_71(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_12_ea(bytes);
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_secret_key_c51(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_d6_7d(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_71(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
decompress_ciphertext_coefficient_2d(__m256i vector) {
=======
decompress_ciphertext_coefficient_87(__m256i vector) {
>>>>>>> main
  __m256i field_modulus =
      mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits =
      mm256_set1_epi32((int32_t)1 << (uint32_t)(int32_t)10);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low =
      mm256_mullo_epi32(coefficients_low0, field_modulus);
  __m256i decompressed_low0 =
      mm256_slli_epi32((int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 =
      mm256_add_epi32(decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 =
      mm256_srli_epi32((int32_t)10, decompressed_low1, __m256i);
  __m256i decompressed_low3 =
      mm256_srli_epi32((int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high =
      mm256_mullo_epi32(coefficients_high0, field_modulus);
  __m256i decompressed_high0 =
      mm256_slli_epi32((int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 =
      mm256_add_epi32(decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 =
      mm256_srli_epi32((int32_t)10, decompressed_high1, __m256i);
  __m256i decompressed_high3 =
      mm256_srli_epi32((int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = mm256_packs_epi32(decompressed_low3, decompressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_09 with const
generics
- COEFFICIENT_BITS= 10
*/
<<<<<<< HEAD
static __m256i decompress_ciphertext_coefficient_09_ac(__m256i vector) {
  return decompress_ciphertext_coefficient_2d(vector);
=======
static __m256i decompress_ciphertext_coefficient_ea_2e(__m256i vector) {
  return decompress_ciphertext_coefficient_87(vector);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_10_56(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
  LowStar_Ignore_ignore(
      Eurydice_slice_len(
          Eurydice_array_to_slice((size_t)16U, re.coefficients, __m256i),
          __m256i),
      size_t, void *);
=======
deserialize_then_decompress_10_5f(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
<<<<<<< HEAD
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_ac(coefficient);
=======
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_2e(coefficient);
>>>>>>> main
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
decompress_ciphertext_coefficient_2d0(__m256i vector) {
=======
decompress_ciphertext_coefficient_870(__m256i vector) {
>>>>>>> main
  __m256i field_modulus =
      mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits =
      mm256_set1_epi32((int32_t)1 << (uint32_t)(int32_t)11);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low =
      mm256_mullo_epi32(coefficients_low0, field_modulus);
  __m256i decompressed_low0 =
      mm256_slli_epi32((int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 =
      mm256_add_epi32(decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 =
      mm256_srli_epi32((int32_t)11, decompressed_low1, __m256i);
  __m256i decompressed_low3 =
      mm256_srli_epi32((int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high =
      mm256_mullo_epi32(coefficients_high0, field_modulus);
  __m256i decompressed_high0 =
      mm256_slli_epi32((int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 =
      mm256_add_epi32(decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 =
      mm256_srli_epi32((int32_t)11, decompressed_high1, __m256i);
  __m256i decompressed_high3 =
      mm256_srli_epi32((int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = mm256_packs_epi32(decompressed_low3, decompressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_09 with const
generics
- COEFFICIENT_BITS= 11
*/
<<<<<<< HEAD
static __m256i decompress_ciphertext_coefficient_09_ac0(__m256i vector) {
  return decompress_ciphertext_coefficient_2d0(vector);
=======
static __m256i decompress_ciphertext_coefficient_ea_2e0(__m256i vector) {
  return decompress_ciphertext_coefficient_870(vector);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_11_42(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
=======
deserialize_then_decompress_11_9a(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t);
<<<<<<< HEAD
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_ac0(coefficient);
=======
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_2e0(coefficient);
>>>>>>> main
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_ring_element_u_d5(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_56(serialized);
=======
deserialize_then_decompress_ring_element_u_f90(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_5f(serialized);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_vector_u_27(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_db(&zeta_i, re);
  ntt_at_layer_2_10(&zeta_i, re);
  ntt_at_layer_1_6e(&zeta_i, re);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void ntt_vector_u_9b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_5f(&zeta_i, re);
  ntt_at_layer_2_c2(&zeta_i, re);
  ntt_at_layer_1_60(&zeta_i, re);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_then_decompress_u_4a1(
=======
static KRML_MUSTINLINE void deserialize_then_decompress_u_9d1(
>>>>>>> main
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
<<<<<<< HEAD
                  u_as_ntt[i] = ZERO_20_1b(););
=======
                  u_as_ntt[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice2(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t);
<<<<<<< HEAD
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_d5(u_bytes);
    ntt_vector_u_27(&u_as_ntt[i0]);
=======
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_f90(u_bytes);
    ntt_vector_u_9b0(&u_as_ntt[i0]);
>>>>>>> main
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
decompress_ciphertext_coefficient_2d1(__m256i vector) {
=======
decompress_ciphertext_coefficient_871(__m256i vector) {
>>>>>>> main
  __m256i field_modulus =
      mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits =
      mm256_set1_epi32((int32_t)1 << (uint32_t)(int32_t)4);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low =
      mm256_mullo_epi32(coefficients_low0, field_modulus);
  __m256i decompressed_low0 =
      mm256_slli_epi32((int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 =
      mm256_add_epi32(decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 =
      mm256_srli_epi32((int32_t)4, decompressed_low1, __m256i);
  __m256i decompressed_low3 =
      mm256_srli_epi32((int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high =
      mm256_mullo_epi32(coefficients_high0, field_modulus);
  __m256i decompressed_high0 =
      mm256_slli_epi32((int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 =
      mm256_add_epi32(decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 =
      mm256_srli_epi32((int32_t)4, decompressed_high1, __m256i);
  __m256i decompressed_high3 =
      mm256_srli_epi32((int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = mm256_packs_epi32(decompressed_low3, decompressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_09 with const
generics
- COEFFICIENT_BITS= 4
*/
<<<<<<< HEAD
static __m256i decompress_ciphertext_coefficient_09_ac1(__m256i vector) {
  return decompress_ciphertext_coefficient_2d1(vector);
=======
static __m256i decompress_ciphertext_coefficient_ea_2e1(__m256i vector) {
  return decompress_ciphertext_coefficient_871(vector);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_4_44(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
=======
deserialize_then_decompress_4_8d(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
<<<<<<< HEAD
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_ac1(coefficient);
=======
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_2e1(coefficient);
>>>>>>> main
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i
<<<<<<< HEAD
decompress_ciphertext_coefficient_2d2(__m256i vector) {
=======
decompress_ciphertext_coefficient_872(__m256i vector) {
>>>>>>> main
  __m256i field_modulus =
      mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits =
      mm256_set1_epi32((int32_t)1 << (uint32_t)(int32_t)5);
  __m128i coefficients_low = mm256_castsi256_si128(vector);
  __m256i coefficients_low0 = mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low =
      mm256_mullo_epi32(coefficients_low0, field_modulus);
  __m256i decompressed_low0 =
      mm256_slli_epi32((int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 =
      mm256_add_epi32(decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 =
      mm256_srli_epi32((int32_t)5, decompressed_low1, __m256i);
  __m256i decompressed_low3 =
      mm256_srli_epi32((int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high =
      mm256_extracti128_si256((int32_t)1, vector, __m128i);
  __m256i coefficients_high0 = mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high =
      mm256_mullo_epi32(coefficients_high0, field_modulus);
  __m256i decompressed_high0 =
      mm256_slli_epi32((int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 =
      mm256_add_epi32(decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 =
      mm256_srli_epi32((int32_t)5, decompressed_high1, __m256i);
  __m256i decompressed_high3 =
      mm256_srli_epi32((int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = mm256_packs_epi32(decompressed_low3, decompressed_high3);
  return mm256_permute4x64_epi64((int32_t)216, compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_09 with const
generics
- COEFFICIENT_BITS= 5
*/
<<<<<<< HEAD
static __m256i decompress_ciphertext_coefficient_09_ac2(__m256i vector) {
  return decompress_ciphertext_coefficient_2d2(vector);
=======
static __m256i decompress_ciphertext_coefficient_ea_2e2(__m256i vector) {
  return decompress_ciphertext_coefficient_872(vector);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_5_f0(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
=======
deserialize_then_decompress_5_c1(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_d6_7d();
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t);
<<<<<<< HEAD
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_09(bytes);
    re.coefficients[i0] =
        decompress_ciphertext_coefficient_09_ac2(re.coefficients[i0]);
=======
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_ea(bytes);
    re.coefficients[i0] =
        decompress_ciphertext_coefficient_ea_2e2(re.coefficients[i0]);
>>>>>>> main
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_ring_element_v_08(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_44(serialized);
=======
deserialize_then_decompress_ring_element_v_590(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_8d(serialized);
>>>>>>> main
}

/**
This function found in impl
<<<<<<< HEAD
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_20
=======
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
subtract_reduce_20_8c(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
=======
subtract_reduce_d6_4a(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
>>>>>>> main
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
<<<<<<< HEAD
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
=======
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
>>>>>>> main
            b.coefficients[i0], (int16_t)1441);
    b.coefficients[i0] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_sub_09(self->coefficients[i0],
                                          &coefficient_normal_form));
  }
  return b;
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_message_3f1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_20_471(&result, &product););
  invert_ntt_montgomery_971(&result);
  result = subtract_reduce_20_8c(v, result);
=======
compute_message_6a1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_b81(&result, &product););
  invert_ntt_montgomery_191(&result);
  result = subtract_reduce_d6_4a(v, result);
>>>>>>> main
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_message_2d(
=======
static KRML_MUSTINLINE void compress_then_serialize_message_53(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
<<<<<<< HEAD
      __m256i coefficient = to_unsigned_representative_4f(re.coefficients[i0]);
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_09(coefficient);
=======
      __m256i coefficient = to_unsigned_representative_c0(re.coefficients[i0]);
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_ea(coefficient);
>>>>>>> main
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_avx2_serialize_1_09(coefficient_compressed, bytes);
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          serialized, (size_t)2U * i0, (size_t)2U * i0 + (size_t)2U, uint8_t);
      Eurydice_slice_copy(uu____0,
                          Eurydice_array_to_slice((size_t)2U, bytes, uint8_t),
                          uint8_t););
  memcpy(ret, serialized, (size_t)32U * sizeof(uint8_t));
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
<<<<<<< HEAD
static void decrypt_unpacked_4c1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  deserialize_then_decompress_u_4a1(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_08(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_3f1(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_2d(message, ret0);
=======
static void decrypt_unpacked_671(IndCpaPrivateKeyUnpacked_a0 *secret_key,
                                 uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  deserialize_then_decompress_u_9d1(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_590(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_6a1(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_53(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_3d1(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  deserialize_secret_key_c51(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[3U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_a0 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_671(&secret_key_unpacked, ciphertext, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_c9(Eurydice_slice input, uint8_t ret[32U]) {
=======
static KRML_MUSTINLINE void PRF_d1(Eurydice_slice input, uint8_t ret[32U]) {
>>>>>>> main
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 3
- LEN= 32
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_263(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_c9(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_d61(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_4c1(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab1(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_173(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_ba_ff0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_263(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
             implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_unpacked_061(uu____3, copy_of_decrypted, pseudorandomness,
                       expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_ba_ff0(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_uncompressed_ring_element_ae(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_20_1b();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_12_09(bytes);
  }
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_secret_key_881(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_20_1b(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_ae(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  memcpy(
      result, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_d21(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  deserialize_secret_key_881(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[3U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_4c1(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void PRF_a9_423(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_d1(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
<<<<<<< HEAD
void libcrux_ml_kem_ind_cca_decapsulate_e21(
=======
void libcrux_ml_kem_ind_cca_decapsulate_971(
>>>>>>> main
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t),
      (size_t)1152U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
<<<<<<< HEAD
  decrypt_d21(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
  decrypt_3d1(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
<<<<<<< HEAD
  G_a9_ab1(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
=======
  G_a9_671(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_173(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_ba_ff0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_263(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
=======
  libcrux_ml_kem_utils_into_padded_array_425(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_fd_ed1(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_423(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
>>>>>>> main
             implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
<<<<<<< HEAD
  encrypt_501(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_6e1(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_af_6e1(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_ba_ff0(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
=======
  encrypt_a41(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_e91(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_e91(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_fd_ed1(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_300(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c3(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
<<<<<<< HEAD
        deserialize_to_reduced_ring_element_55(ring_element);
=======
        deserialize_to_reduced_ring_element_1b(ring_element);
>>>>>>> main
    deserialized_pk[i0] = uu____0;
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1568
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_660(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_d6_7d(););
  deserialize_ring_elements_reduced_8c3(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- OUT_LEN= 1536
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_secret_key_500(
=======
static KRML_MUSTINLINE void serialize_secret_key_5f(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[1536U]) {
  uint8_t out[1536U] = {0U};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret0[384U];
<<<<<<< HEAD
    serialize_uncompressed_ring_element_5c(&re, ret0);
=======
    serialize_uncompressed_ring_element_53(&re, ret0);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)1536U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_c2(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)1536U, uint8_t);
  uint8_t ret[1536U];
  serialize_secret_key_5f(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1536U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1568U, serialized, (size_t)1536U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_public_key_510(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)1536U, uint8_t);
  uint8_t ret0[1536U];
  serialize_secret_key_500(t_as_ntt, ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1536U, ret0, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key_serialized,
                                      (size_t)1536U, uint8_t, size_t),
      seed_for_a, uint8_t);
  uint8_t result[1568U];
  memcpy(result, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)1568U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void serialize_public_key_02(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  serialize_public_key_mut_c2(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
>>>>>>> main
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
<<<<<<< HEAD
bool libcrux_ml_kem_ind_cca_validate_public_key_060(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  deserialize_ring_elements_reduced_300(
=======
bool libcrux_ml_kem_ind_cca_validate_public_key_050(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  deserialize_ring_elements_reduced_out_660(
>>>>>>> main
      Eurydice_array_to_subslice_to((size_t)1568U, public_key, (size_t)1536U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
<<<<<<< HEAD
  serialize_public_key_510(
=======
  serialize_public_key_02(
>>>>>>> main
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1568U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 4
*/
static KRML_MUSTINLINE void H_a9_16(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_4d0(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *_ciphertext) {
  uint8_t t[32U];
  H_a9_16(Eurydice_array_to_subslice2(
              private_key->value, (size_t)384U * (size_t)4U,
              (size_t)768U * (size_t)4U + (size_t)32U, uint8_t),
          t);
  Eurydice_slice expected = Eurydice_array_to_subslice2(
      private_key->value, (size_t)768U * (size_t)4U + (size_t)32U,
      (size_t)768U * (size_t)4U + (size_t)64U, uint8_t);
  return core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq(
      (size_t)32U, t, &expected, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_01_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
} IndCpaPrivateKeyUnpacked_01;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_1a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static IndCpaPrivateKeyUnpacked_01 default_1a_19(void) {
  IndCpaPrivateKeyUnpacked_01 lit;
  lit.secret_as_ntt[0U] = ZERO_d6_7d();
  lit.secret_as_ntt[1U] = ZERO_d6_7d();
  lit.secret_as_ntt[2U] = ZERO_d6_7d();
  lit.secret_as_ntt[3U] = ZERO_d6_7d();
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct IndCpaPublicKeyUnpacked_01_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
} IndCpaPublicKeyUnpacked_01;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8d
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static IndCpaPublicKeyUnpacked_01 default_8d_80(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  uu____0[i] = ZERO_d6_7d(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_01 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_d6_7d();
  lit.A[0U][1U] = ZERO_d6_7d();
  lit.A[0U][2U] = ZERO_d6_7d();
  lit.A[0U][3U] = ZERO_d6_7d();
  lit.A[1U][0U] = ZERO_d6_7d();
  lit.A[1U][1U] = ZERO_d6_7d();
  lit.A[1U][2U] = ZERO_d6_7d();
  lit.A[1U][3U] = ZERO_d6_7d();
  lit.A[2U][0U] = ZERO_d6_7d();
  lit.A[2U][1U] = ZERO_d6_7d();
  lit.A[2U][2U] = ZERO_d6_7d();
  lit.A[2U][3U] = ZERO_d6_7d();
  lit.A[3U][0U] = ZERO_d6_7d();
  lit.A[3U][1U] = ZERO_d6_7d();
  lit.A[3U][2U] = ZERO_d6_7d();
  lit.A[3U][3U] = ZERO_d6_7d();
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void G_a9_ab0(Eurydice_slice input, uint8_t ret[64U]) {
=======
static KRML_MUSTINLINE void G_a9_67(Eurydice_slice input, uint8_t ret[64U]) {
>>>>>>> main
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
<<<<<<< HEAD
static void closure_ba0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void cpa_keygen_seed_d8_e1(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  uint8_t ret0[64U];
  G_a9_67(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_500(uint8_t input[4U][34U]) {
=======
shake128_init_absorb_2a(uint8_t input[4U][34U]) {
>>>>>>> main
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[3U], uint8_t));
  return state;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_a9 with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_a9_3f0(uint8_t input[4U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[4U][34U];
  memcpy(copy_of_input, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_500(copy_of_input);
=======
shake128_init_absorb_a9_1c(uint8_t input[4U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[4U][34U];
  memcpy(copy_of_input, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_2a(copy_of_input);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_000(
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_0c(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[4U][504U]) {
  uint8_t out[4U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t));
  uint8_t uu____0[504U];
  memcpy(uu____0, out0, (size_t)504U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____1[504U];
  memcpy(uu____1, out1, (size_t)504U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____2[504U];
  memcpy(uu____2, out2, (size_t)504U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____3[504U];
  memcpy(uu____3, out3, (size_t)504U * sizeof(uint8_t));
  memcpy(out[3U], uu____3, (size_t)504U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_a9 with
const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_940(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_first_three_blocks_000(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_a9_2e(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_three_blocks_0c(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- N= 504
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_611(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_74(
>>>>>>> main
    uint8_t randomness[4U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block with const
generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_dd0(
=======
static KRML_MUSTINLINE void shake128_squeeze_block_4a(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[4U][168U]) {
  uint8_t out[4U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  uint8_t uu____0[168U];
  memcpy(uu____0, out0, (size_t)168U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____1[168U];
  memcpy(uu____1, out1, (size_t)168U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____2[168U];
  memcpy(uu____2, out2, (size_t)168U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____3[168U];
  memcpy(uu____3, out3, (size_t)168U * sizeof(uint8_t));
  memcpy(out[3U], uu____3, (size_t)168U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_a9 with const
generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_bf0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_next_block_dd0(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_block_a9_1d(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_block_4a(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- N= 168
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_612(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_740(
>>>>>>> main
    uint8_t randomness[4U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
<<<<<<< HEAD
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_8a0(
    int16_t s[272U]) {
  return from_i16_array_20_82(
=======
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_e4(
    int16_t s[272U]) {
  return from_i16_array_d6_14(
>>>>>>> main
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_from_xof_c10(
=======
static KRML_MUSTINLINE void sample_from_xof_67(
>>>>>>> main
    uint8_t seeds[4U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[4U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)4U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
<<<<<<< HEAD
      shake128_init_absorb_final_a9_3f0(copy_of_seeds);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_first_three_blocks_a9_940(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[4U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_611(
=======
      shake128_init_absorb_a9_1c(copy_of_seeds);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_three_blocks_a9_2e(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[4U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_74(
>>>>>>> main
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
<<<<<<< HEAD
      shake128_squeeze_next_block_a9_bf0(&xof_state, randomness);
=======
      shake128_squeeze_block_a9_1d(&xof_state, randomness);
>>>>>>> main
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[4U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)4U * sizeof(uint8_t[168U]));
<<<<<<< HEAD
      done = sample_from_uniform_distribution_next_612(
=======
      done = sample_from_uniform_distribution_next_740(
>>>>>>> main
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[4U][272U];
  memcpy(copy_of_out, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
<<<<<<< HEAD
                  ret0[i] = closure_8a0(copy_of_out[i]););
=======
                  ret0[i] = closure_e4(copy_of_out[i]););
>>>>>>> main
  memcpy(
      ret, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_matrix_A_ff0(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U][4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  closure_ba0(A_transpose[i]););
=======
static KRML_MUSTINLINE void sample_matrix_A_34(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[4U],
    uint8_t seed[34U], bool transpose) {
>>>>>>> main
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seed[34U];
      memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[4U][34U]; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seeds[4U][34U];
      memcpy(copy_of_seeds, seeds, (size_t)4U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[4U];
<<<<<<< HEAD
      sample_from_xof_c10(copy_of_seeds, sampled);
=======
      sample_from_xof_67(copy_of_seeds, sampled);
>>>>>>> main
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)4U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      }

  );
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U][4U];
  memcpy(result, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  memcpy(ret, result,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
=======
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 4
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_ef1(uint8_t (*input)[33U],
                                      uint8_t ret[4U][128U]) {
=======
static KRML_MUSTINLINE void PRFxN_08(uint8_t (*input)[33U],
                                     uint8_t ret[4U][128U]) {
>>>>>>> main
  uint8_t out[4U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[3U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t));
  uint8_t uu____0[128U];
  memcpy(uu____0, out0, (size_t)128U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____1[128U];
  memcpy(uu____1, out1, (size_t)128U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____2[128U];
  memcpy(uu____2, out2, (size_t)128U * sizeof(uint8_t));
  memcpy(out[2U], uu____2, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____3[128U];
  memcpy(uu____3, out3, (size_t)128U * sizeof(uint8_t));
  memcpy(out[3U], uu____3, (size_t)128U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_a9
with const generics
- K= 4
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_a9_411(uint8_t (*input)[33U],
                                         uint8_t ret[4U][128U]) {
  PRFxN_ef1(input, ret);
=======
static KRML_MUSTINLINE void PRFxN_a9_16(uint8_t (*input)[33U],
                                        uint8_t ret[4U][128U]) {
  PRFxN_08(input, ret);
>>>>>>> main
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE tuple_71 sample_vector_cbd_then_ntt_e40(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  re_as_ntt[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_ee(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[4U][128U];
<<<<<<< HEAD
  PRFxN_a9_411(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_8e0(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_0d(&re_as_ntt[i0]););
=======
  PRFxN_a9_16(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_af(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_d5(&re_as_ntt[i0]););
  return domain_separator;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[4size_t], uint8_t

*/
typedef struct tuple_71_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 fst[4U];
  uint8_t snd;
} tuple_71;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt_out
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_71 sample_vector_cbd_then_ntt_out_7f(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  re_as_ntt[i] = ZERO_d6_7d(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_ee(uu____0, uu____1, domain_separator);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[4U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 result;
  memcpy(
<<<<<<< HEAD
      result.fst, copy_of_re_as_ntt,
=======
      lit.fst, copy_of_re_as_ntt,
>>>>>>> main
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
<<<<<<< HEAD
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_20
=======
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void add_to_ring_element_20_470(
=======
static KRML_MUSTINLINE void add_to_ring_element_d6_b8(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, self->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_09(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_As_plus_e_ef0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result0[i] = ZERO_20_1b(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)4U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_20_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_20_470(&result0[i1], &product);
    }
    add_standard_error_reduce_20_f6(&result0[i1], &error_as_ntt[i1]);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U];
  memcpy(
      result, result0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
=======
static KRML_MUSTINLINE void compute_As_plus_e_a2(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_d6_7d();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)4U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_d6_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_b8(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_a7(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
>>>>>>> main
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static tuple_54 generate_keypair_unpacked_470(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_ab0(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
=======
static void generate_keypair_unpacked_81(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_01 *private_key,
    IndCpaPublicKeyUnpacked_01 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_e1(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
>>>>>>> main
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[4U] =
      public_key->A;
  uint8_t ret[34U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_171(seed_for_A0, ret);
  sample_matrix_A_ff0(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(seed_for_secret_and_error,
                                             prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____2 = sample_vector_cbd_then_ntt_e40(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
=======
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_34(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_ee(uu____2, copy_of_prf_input0, 0U);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[4U];
  memcpy(
      error_as_ntt,
<<<<<<< HEAD
      sample_vector_cbd_then_ntt_e40(copy_of_prf_input, domain_separator).fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  compute_As_plus_e_ef0(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[4U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A_transpose[4U]
                                                                        [4U];
  memcpy(copy_of_A_transpose, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 pk;
  memcpy(
      pk.t_as_ntt, copy_of_t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, copy_of_seed_for_A, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, copy_of_A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[4U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 sk;
  memcpy(
      sk.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_54){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void closure_1c0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 4
*/
static KRML_MUSTINLINE void H_a9_310(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_450(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  tuple_54 uu____0 = generate_keypair_unpacked_470(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, closure_1c0(A[i]););
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_3a_33(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[4U][4U];
  memcpy(uu____2, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  uint8_t pk_serialized[1568U];
  serialize_public_key_510(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_310(Eurydice_array_to_slice((size_t)1568U, pk_serialized, uint8_t),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U]);
  core_result_unwrap_41_33(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 uu____3 =
      ind_cpa_private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_implicit_rejection_value[32U];
  memcpy(copy_of_implicit_rejection_value, implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_01 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, copy_of_implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 uu____6 =
      ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_hash[32U];
  memcpy(copy_of_public_key_hash, public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, copy_of_public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  return lit;
=======
      sample_vector_cbd_then_ntt_out_7f(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_a2(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static libcrux_ml_kem_utils_extraction_helper_Keypair1024 generate_keypair_930(
    Eurydice_slice key_generation_seed) {
  tuple_54 uu____0 = generate_keypair_unpacked_470(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 pk = uu____0.snd;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_510(
      pk.t_as_ntt, Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key_500(sk.secret_as_ntt, secret_key_serialized);
=======
static libcrux_ml_kem_utils_extraction_helper_Keypair1024 generate_keypair_2f0(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_01 private_key = default_1a_19();
  IndCpaPublicKeyUnpacked_01 public_key = default_8d_80();
  generate_keypair_unpacked_81(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1568U];
  serialize_public_key_02(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key_5f(private_key.secret_as_ntt, secret_key_serialized);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1536U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1568U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
<<<<<<< HEAD
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  return result;
=======
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_kem_secret_key_eb0(
=======
static KRML_MUSTINLINE void serialize_kem_secret_key_0a0(
>>>>>>> main
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[3168U]) {
  uint8_t out[3168U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t);
  uint8_t ret0[32U];
<<<<<<< HEAD
  H_a9_310(public_key, ret0);
=======
  H_a9_16(public_key, ret0);
>>>>>>> main
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
  memcpy(ret, out, (size_t)3168U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
<<<<<<< HEAD
libcrux_ml_kem_ind_cca_generate_keypair_f70(uint8_t randomness[64U]) {
=======
libcrux_ml_kem_ind_cca_generate_keypair_510(uint8_t randomness[64U]) {
>>>>>>> main
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
<<<<<<< HEAD
      generate_keypair_930(ind_cpa_keypair_randomness);
=======
      generate_keypair_2f0(ind_cpa_keypair_randomness);
>>>>>>> main
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
<<<<<<< HEAD
  serialize_kem_secret_key_eb0(
=======
  serialize_kem_secret_key_0a0(
>>>>>>> main
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[3168U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_95 private_key =
<<<<<<< HEAD
      libcrux_ml_kem_types_from_e7_f11(copy_of_secret_key_serialized);
=======
      libcrux_ml_kem_types_from_88_2d1(copy_of_secret_key_serialized);
>>>>>>> main
  libcrux_ml_kem_types_MlKemPrivateKey_95 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1568U];
  memcpy(copy_of_public_key, public_key, (size_t)1568U * sizeof(uint8_t));
<<<<<<< HEAD
  return libcrux_ml_kem_types_from_64_b11(
      uu____2, libcrux_ml_kem_types_from_07_a91(copy_of_public_key));
=======
  return libcrux_ml_kem_types_from_17_8b1(
      uu____2, libcrux_ml_kem_types_from_40_601(copy_of_public_key));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_d8_960(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1536
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_1b(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_71
<<<<<<< HEAD
sample_ring_element_cbd_e70(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_20_1b(););
=======
sample_ring_element_cbd_c6(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_d6_7d(););
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[4U][128U];
<<<<<<< HEAD
  PRFxN_a9_411(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_8e0(
=======
  PRFxN_a9_16(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_af(
>>>>>>> main
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[4U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 result;
  memcpy(
<<<<<<< HEAD
      result.fst, copy_of_error_1,
=======
      lit.fst, copy_of_error_1,
>>>>>>> main
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 4
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_262(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_c90(input, ret);
=======
static KRML_MUSTINLINE void PRF_a9_420(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_d10(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_montgomery_970(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_16(&zeta_i, re);
  invert_ntt_at_layer_2_88(&zeta_i, re);
  invert_ntt_at_layer_3_f7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void invert_ntt_montgomery_19(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_2b(&zeta_i, re);
  invert_ntt_at_layer_2_6a(&zeta_i, re);
  invert_ntt_at_layer_3_ad(&zeta_i, re);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_vector_u_e30(
=======
static KRML_MUSTINLINE void compute_vector_u_ba(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
<<<<<<< HEAD
                  result0[i] = ZERO_20_1b(););
=======
                  result[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)4U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
<<<<<<< HEAD
          ntt_multiply_20_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_20_470(&result0[i1], &product);
    }
    invert_ntt_montgomery_970(&result0[i1]);
    add_error_reduce_20_1f(&result0[i1], &error_1[i1]);
=======
          ntt_multiply_d6_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_b8(&result[i1], &product);
    }
    invert_ntt_montgomery_19(&result[i1]);
    add_error_reduce_d6_89(&result[i1], &error_1[i1]);
>>>>>>> main
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U];
  memcpy(
      result, result0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_ring_element_v_e70(
=======
compute_ring_element_v_9f(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_20_470(&result, &product););
  invert_ntt_montgomery_970(&result);
  result = add_message_error_reduce_20_69(error_2, message, result);
=======
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_b8(&result, &product););
  invert_ntt_montgomery_19(&result);
  result = add_message_error_reduce_d6_df(error_2, message, result);
>>>>>>> main
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 352
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_11_770(
=======
static KRML_MUSTINLINE void compress_then_serialize_11_88(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
<<<<<<< HEAD
        compress_09_760(to_unsigned_representative_4f(re->coefficients[i0]));
=======
        compress_ea_ab0(to_unsigned_representative_c0(re->coefficients[i0]));
>>>>>>> main
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2_serialize_11_09(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)22U * i0, (size_t)22U * i0 + (size_t)22U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)22U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)352U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_810(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_770(re, uu____0);
=======
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_88(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_88(re, uu____0);
>>>>>>> main
  memcpy(ret, uu____0, (size_t)352U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- OUT_LEN= 1408
- COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
<<<<<<< HEAD
static void compress_then_serialize_u_9f0(
=======
static void compress_then_serialize_u_0b(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[4U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t);
    uint8_t ret[352U];
<<<<<<< HEAD
    compress_then_serialize_ring_element_u_810(&re, ret);
=======
    compress_then_serialize_ring_element_u_88(&re, ret);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)352U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_0c0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_5_2c(re, out);
=======
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_f3(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_5_a4(re, out);
>>>>>>> main
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_unpacked_060(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____1 = sample_vector_cbd_then_ntt_e40(copy_of_prf_input0, 0U);
=======
static void encrypt_unpacked_be(IndCpaPublicKeyUnpacked_01 *public_key,
                                uint8_t message[32U], Eurydice_slice randomness,
                                uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____1 = sample_vector_cbd_then_ntt_out_7f(copy_of_prf_input0, 0U);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____3 =
<<<<<<< HEAD
      sample_ring_element_cbd_e70(copy_of_prf_input, domain_separator0);
=======
      sample_ring_element_cbd_c6(copy_of_prf_input, domain_separator0);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
<<<<<<< HEAD
  PRF_a9_262(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_8e0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[4U];
  compute_vector_u_e30(public_key->A, r_as_ntt, error_1, u);
=======
  PRF_a9_420(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_af(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[4U];
  compute_vector_u_ba(public_key->A, r_as_ntt, error_1, u);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
<<<<<<< HEAD
      deserialize_then_decompress_message_e3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_e70(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
=======
      deserialize_then_decompress_message_ef(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_9f(public_key->t_as_ntt, r_as_ntt, &error_2,
                                &message_as_ring_element);
>>>>>>> main
  uint8_t ciphertext[1568U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[4U];
  memcpy(
      uu____5, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
<<<<<<< HEAD
  compress_then_serialize_u_9f0(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                           (size_t)1408U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_0c0(
=======
  compress_then_serialize_u_0b(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                           (size_t)1408U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_f3(
>>>>>>> main
      uu____6, Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                               (size_t)1408U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

/**
<<<<<<< HEAD
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- VECTOR_U_BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_21 libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_250(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  Eurydice_slice_copy(uu____0,
                      Eurydice_array_to_slice(
                          (size_t)32U, public_key->public_key_hash, uint8_t),
                      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____2 =
      &public_key->ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_unpacked_060(uu____2, copy_of_randomness, pseudorandomness,
                       ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 =
      libcrux_ml_kem_types_from_15_e91(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_21 lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.entropy_preprocess_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_af_150(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, randomness, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
}

/**
=======
>>>>>>> main
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_500(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1568U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  deserialize_ring_elements_reduced_300(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t),
      t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1536U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_171(seed, ret0);
  sample_matrix_A_ff0(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[4U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A[4U][4U];
  memcpy(copy_of_A, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, copy_of_t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, copy_of_seed_for_A,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, copy_of_A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____3 =
      &public_key_unpacked;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[1568U];
  encrypt_unpacked_060(uu____3, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)1568U * sizeof(uint8_t));
=======
static void encrypt_a40(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1568U]) {
  IndCpaPublicKeyUnpacked_01 unpacked_public_key = default_8d_80();
  deserialize_ring_elements_reduced_8c(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1536U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[4U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_34(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_01 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1568U];
  encrypt_unpacked_be(uu____1, copy_of_message, randomness, ret1);
  memcpy(ret, ret1, (size_t)1568U * sizeof(uint8_t));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void kdf_af_6e0(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, shared_secret, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
=======
static KRML_MUSTINLINE void kdf_d8_e90(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_b30(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_150(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_9c0(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_960(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
<<<<<<< HEAD
  H_a9_310(Eurydice_array_to_slice(
               (size_t)1568U, libcrux_ml_kem_types_as_slice_f6_ae1(public_key),
               uint8_t),
           ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_ab0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
=======
  H_a9_16(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_ba_12(public_key),
              uint8_t),
          ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_67(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
<<<<<<< HEAD
      (size_t)1568U, libcrux_ml_kem_types_as_slice_f6_ae1(public_key), uint8_t);
=======
      (size_t)1568U, libcrux_ml_kem_types_as_slice_ba_12(public_key), uint8_t);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
<<<<<<< HEAD
  encrypt_500(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_15_e91(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_af_6e0(shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 = ciphertext0;
=======
  encrypt_a40(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_1f ciphertext0 =
      libcrux_ml_kem_types_from_fc_36(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_e90(shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext_1f uu____5 = ciphertext0;
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
<<<<<<< HEAD
  tuple_21 result;
  result.fst = uu____5;
  memcpy(result.snd, copy_of_shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  return result;
=======
  tuple_21 lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_secret_key_c50(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_d6_7d(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_71(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_ring_element_u_d50(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_42(serialized);
=======
deserialize_then_decompress_ring_element_u_f9(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_9a(serialized);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void ntt_vector_u_270(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_0d(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_db(&zeta_i, re);
  ntt_at_layer_2_10(&zeta_i, re);
  ntt_at_layer_1_6e(&zeta_i, re);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void ntt_vector_u_9b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_5f(&zeta_i, re);
  ntt_at_layer_2_c2(&zeta_i, re);
  ntt_at_layer_1_60(&zeta_i, re);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_then_decompress_u_4a0(
=======
static KRML_MUSTINLINE void deserialize_then_decompress_u_9d(
>>>>>>> main
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
<<<<<<< HEAD
                  u_as_ntt[i] = ZERO_20_1b(););
=======
                  u_as_ntt[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice2(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U,
        uint8_t);
<<<<<<< HEAD
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_d50(u_bytes);
    ntt_vector_u_270(&u_as_ntt[i0]);
=======
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_f9(u_bytes);
    ntt_vector_u_9b(&u_as_ntt[i0]);
>>>>>>> main
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
deserialize_then_decompress_ring_element_v_080(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_f0(serialized);
=======
deserialize_then_decompress_ring_element_v_59(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_c1(serialized);
>>>>>>> main
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_message_3f0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_20_470(&result, &product););
  invert_ntt_montgomery_970(&result);
  result = subtract_reduce_20_8c(v, result);
=======
compute_message_6a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_b8(&result, &product););
  invert_ntt_montgomery_19(&result);
  result = subtract_reduce_d6_4a(v, result);
>>>>>>> main
  return result;
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
<<<<<<< HEAD
static void decrypt_unpacked_4c0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  deserialize_then_decompress_u_4a0(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_080(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_3f0(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_2d(message, ret0);
=======
static void decrypt_unpacked_67(IndCpaPrivateKeyUnpacked_01 *secret_key,
                                uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  deserialize_then_decompress_u_9d(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_59(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_6a(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_53(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static void decrypt_3d0(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  deserialize_secret_key_c50(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[4U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_01 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_67(&secret_key_unpacked, ciphertext, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 4
- LEN= 32
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_261(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_c9(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_d60(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_4c0(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_174(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_ba_ff1(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_261(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
             implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_unpacked_060(uu____3, copy_of_decrypted, pseudorandomness,
                       expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_ba_ff1(ciphertext),
          Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_secret_key_880(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_20_1b(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_ae(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U];
  memcpy(
      result, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static void decrypt_d20(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  deserialize_secret_key_880(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[4U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_4c0(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void PRF_a9_42(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_d1(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
<<<<<<< HEAD
void libcrux_ml_kem_ind_cca_decapsulate_e20(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
=======
void libcrux_ml_kem_ind_cca_decapsulate_970(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *ciphertext, uint8_t ret[32U]) {
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t),
      (size_t)1536U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1568U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
<<<<<<< HEAD
  decrypt_d20(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
  decrypt_3d0(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
<<<<<<< HEAD
  G_a9_ab0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
=======
  G_a9_67(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1600U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_174(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_ba_ff1(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_261(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
             implicit_rejection_shared_secret0);
=======
  libcrux_ml_kem_utils_into_padded_array_420(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_fd_ed(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_42(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
>>>>>>> main
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
<<<<<<< HEAD
  encrypt_500(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_6e0(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_af_6e0(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_ba_ff1(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
=======
  encrypt_a40(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_e90(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_e90(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_fd_ed(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_30(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c2(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
<<<<<<< HEAD
        deserialize_to_reduced_ring_element_55(ring_element);
=======
        deserialize_to_reduced_ring_element_1b(ring_element);
>>>>>>> main
    deserialized_pk[i0] = uu____0;
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 800
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_66(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_d6_7d(););
  deserialize_ring_elements_reduced_8c2(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- OUT_LEN= 768
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_secret_key_50(
=======
static KRML_MUSTINLINE void serialize_secret_key_5f0(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[768U]) {
  uint8_t out[768U] = {0U};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret0[384U];
<<<<<<< HEAD
    serialize_uncompressed_ring_element_5c(&re, ret0);
=======
    serialize_uncompressed_ring_element_53(&re, ret0);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)768U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_mut_c20(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)768U, uint8_t);
  uint8_t ret[768U];
  serialize_secret_key_5f0(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)768U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)800U, serialized, (size_t)768U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_public_key_51(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)768U, uint8_t);
  uint8_t ret0[768U];
  serialize_secret_key_50(t_as_ntt, ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)768U, ret0, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)800U, public_key_serialized,
                                      (size_t)768U, uint8_t, size_t),
      seed_for_a, uint8_t);
  uint8_t result[800U];
  memcpy(result, public_key_serialized, (size_t)800U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)800U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void serialize_public_key_020(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  serialize_public_key_mut_c20(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)800U * sizeof(uint8_t));
>>>>>>> main
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
<<<<<<< HEAD
bool libcrux_ml_kem_ind_cca_validate_public_key_06(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  deserialize_ring_elements_reduced_30(
=======
bool libcrux_ml_kem_ind_cca_validate_public_key_05(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  deserialize_ring_elements_reduced_out_66(
>>>>>>> main
      Eurydice_array_to_subslice_to((size_t)800U, public_key, (size_t)768U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
<<<<<<< HEAD
  serialize_public_key_51(
=======
  serialize_public_key_020(
>>>>>>> main
      uu____0,
      Eurydice_array_to_subslice_from((size_t)800U, public_key, (size_t)768U,
                                      uint8_t, size_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)800U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 2
*/
static KRML_MUSTINLINE void H_a9_160(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_4d(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *_ciphertext) {
  uint8_t t[32U];
  H_a9_160(Eurydice_array_to_subslice2(
               private_key->value, (size_t)384U * (size_t)2U,
               (size_t)768U * (size_t)2U + (size_t)32U, uint8_t),
           t);
  Eurydice_slice expected = Eurydice_array_to_subslice2(
      private_key->value, (size_t)768U * (size_t)2U + (size_t)32U,
      (size_t)768U * (size_t)2U + (size_t)64U, uint8_t);
  return core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq(
      (size_t)32U, t, &expected, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_d6_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
} IndCpaPrivateKeyUnpacked_d6;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_1a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static IndCpaPrivateKeyUnpacked_d6 default_1a_190(void) {
  IndCpaPrivateKeyUnpacked_d6 lit;
  lit.secret_as_ntt[0U] = ZERO_d6_7d();
  lit.secret_as_ntt[1U] = ZERO_d6_7d();
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct IndCpaPublicKeyUnpacked_d6_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
} IndCpaPublicKeyUnpacked_d6;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8d
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static IndCpaPublicKeyUnpacked_d6 default_8d_800(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  uu____0[i] = ZERO_d6_7d(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_d6 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_d6_7d();
  lit.A[0U][1U] = ZERO_d6_7d();
  lit.A[1U][0U] = ZERO_d6_7d();
  lit.A[1U][1U] = ZERO_d6_7d();
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void G_a9_ab(Eurydice_slice input, uint8_t ret[64U]) {
=======
static KRML_MUSTINLINE void G_a9_670(Eurydice_slice input, uint8_t ret[64U]) {
>>>>>>> main
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
<<<<<<< HEAD
static void closure_ba(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE void cpa_keygen_seed_d8_e10(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)2U;
  uint8_t ret0[64U];
  G_a9_670(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_50(uint8_t input[2U][34U]) {
=======
shake128_init_absorb_2a0(uint8_t input[2U][34U]) {
>>>>>>> main
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t));
  return state;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_a9 with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
<<<<<<< HEAD
shake128_init_absorb_final_a9_3f(uint8_t input[2U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[2U][34U];
  memcpy(copy_of_input, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_50(copy_of_input);
=======
shake128_init_absorb_a9_1c0(uint8_t input[2U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[2U][34U];
  memcpy(copy_of_input, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_2a0(copy_of_input);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_00(
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_0c0(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[2U][504U]) {
  uint8_t out[2U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t));
  uint8_t uu____0[504U];
  memcpy(uu____0, out0, (size_t)504U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)504U * sizeof(uint8_t));
  uint8_t uu____1[504U];
  memcpy(uu____1, out1, (size_t)504U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)504U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_a9 with
const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_94(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_first_three_blocks_00(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_a9_2e0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_three_blocks_0c0(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- N= 504
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_61(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_741(
>>>>>>> main
    uint8_t randomness[2U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block with const
generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_dd(
=======
static KRML_MUSTINLINE void shake128_squeeze_block_4a0(
>>>>>>> main
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[2U][168U]) {
  uint8_t out[2U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  uint8_t uu____0[168U];
  memcpy(uu____0, out0, (size_t)168U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)168U * sizeof(uint8_t));
  uint8_t uu____1[168U];
  memcpy(uu____1, out1, (size_t)168U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)168U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_a9 with const
generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_bf(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_next_block_dd(self, ret);
=======
static KRML_MUSTINLINE void shake128_squeeze_block_a9_1d0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_block_4a0(self, ret);
>>>>>>> main
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- N= 168
*/
<<<<<<< HEAD
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_610(
=======
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_742(
>>>>>>> main
    uint8_t randomness[2U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
              randomness[i1], r * (size_t)24U, r * (size_t)24U + (size_t)24U,
              uint8_t);
<<<<<<< HEAD
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
=======
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
>>>>>>> main
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t));
          size_t uu____1 = i1;
          sampled_coefficients[uu____1] =
              sampled_coefficients[uu____1] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
<<<<<<< HEAD
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_8a(
    int16_t s[272U]) {
  return from_i16_array_20_82(
=======
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_e40(
    int16_t s[272U]) {
  return from_i16_array_d6_14(
>>>>>>> main
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_from_xof_c1(
=======
static KRML_MUSTINLINE void sample_from_xof_670(
>>>>>>> main
    uint8_t seeds[2U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[2U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)2U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
<<<<<<< HEAD
      shake128_init_absorb_final_a9_3f(copy_of_seeds);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_first_three_blocks_a9_94(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[2U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_61(
=======
      shake128_init_absorb_a9_1c0(copy_of_seeds);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_three_blocks_a9_2e0(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[2U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_741(
>>>>>>> main
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
<<<<<<< HEAD
      shake128_squeeze_next_block_a9_bf(&xof_state, randomness);
=======
      shake128_squeeze_block_a9_1d0(&xof_state, randomness);
>>>>>>> main
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[2U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)2U * sizeof(uint8_t[168U]));
<<<<<<< HEAD
      done = sample_from_uniform_distribution_next_610(
=======
      done = sample_from_uniform_distribution_next_742(
>>>>>>> main
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[2U][272U];
  memcpy(copy_of_out, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
<<<<<<< HEAD
                  ret0[i] = closure_8a(copy_of_out[i]););
=======
                  ret0[i] = closure_e40(copy_of_out[i]););
>>>>>>> main
  memcpy(
      ret, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void sample_matrix_A_ff(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U][2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  closure_ba(A_transpose[i]););
=======
static KRML_MUSTINLINE void sample_matrix_A_340(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[2U],
    uint8_t seed[34U], bool transpose) {
>>>>>>> main
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seed[34U];
      memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[2U][34U]; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_seeds[2U][34U];
      memcpy(copy_of_seeds, seeds, (size_t)2U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[2U];
<<<<<<< HEAD
      sample_from_xof_c1(copy_of_seeds, sampled);
=======
      sample_from_xof_670(copy_of_seeds, sampled);
>>>>>>> main
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)2U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      }

  );
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U][2U];
  memcpy(result, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  memcpy(ret, result,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
=======
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 192
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_ef(uint8_t (*input)[33U],
                                     uint8_t ret[2U][192U]) {
=======
static KRML_MUSTINLINE void PRFxN_080(uint8_t (*input)[33U],
                                      uint8_t ret[2U][192U]) {
>>>>>>> main
  uint8_t out[2U][192U] = {{0U}};
  uint8_t out0[192U] = {0U};
  uint8_t out1[192U] = {0U};
  uint8_t out2[192U] = {0U};
  uint8_t out3[192U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)192U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)192U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)192U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)192U, out3, uint8_t));
  uint8_t uu____0[192U];
  memcpy(uu____0, out0, (size_t)192U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)192U * sizeof(uint8_t));
  uint8_t uu____1[192U];
  memcpy(uu____1, out1, (size_t)192U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)192U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[192U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_a9
with const generics
- K= 2
- LEN= 192
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_a9_41(uint8_t (*input)[33U],
                                        uint8_t ret[2U][192U]) {
  PRFxN_ef(input, ret);
=======
static KRML_MUSTINLINE void PRFxN_a9_160(uint8_t (*input)[33U],
                                         uint8_t ret[2U][192U]) {
  PRFxN_080(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
sample_from_binomial_distribution_8e(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_5f(randomness);
=======
sample_from_binomial_distribution_af0(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_3c(randomness);
>>>>>>> main
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
<<<<<<< HEAD
static KRML_MUSTINLINE tuple_74 sample_vector_cbd_then_ntt_e4(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  re_as_ntt[i] = ZERO_20_1b(););
=======
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_ee0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[2U][192U];
<<<<<<< HEAD
  PRFxN_a9_41(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_8e(
          Eurydice_array_to_slice((size_t)192U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_0d(&re_as_ntt[i0]););
=======
  PRFxN_a9_160(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_af0(
          Eurydice_array_to_slice((size_t)192U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_d5(&re_as_ntt[i0]););
  return domain_separator;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[2size_t], uint8_t

*/
typedef struct tuple_74_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 fst[2U];
  uint8_t snd;
} tuple_74;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt_out
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE tuple_74 sample_vector_cbd_then_ntt_out_7f0(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  re_as_ntt[i] = ZERO_d6_7d(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_ee0(uu____0, uu____1, domain_separator);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[2U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 result;
  memcpy(
<<<<<<< HEAD
      result.fst, copy_of_re_as_ntt,
=======
      lit.fst, copy_of_re_as_ntt,
>>>>>>> main
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
<<<<<<< HEAD
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_20
=======
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
>>>>>>> main
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void add_to_ring_element_20_47(
=======
static KRML_MUSTINLINE void add_to_ring_element_d6_b80(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, self->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_09(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_As_plus_e_ef(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result0[i] = ZERO_20_1b(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)2U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_20_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_20_47(&result0[i1], &product);
    }
    add_standard_error_reduce_20_f6(&result0[i1], &error_as_ntt[i1]);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U];
  memcpy(
      result, result0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
=======
static KRML_MUSTINLINE void compute_As_plus_e_a20(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_d6_7d();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)2U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_d6_f1(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_b80(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_a7(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
>>>>>>> main
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
<<<<<<< HEAD
static tuple_4c generate_keypair_unpacked_47(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_ab(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
=======
static void generate_keypair_unpacked_810(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_d6 *private_key,
    IndCpaPublicKeyUnpacked_d6 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_e10(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
>>>>>>> main
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[2U] =
      public_key->A;
  uint8_t ret[34U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_171(seed_for_A0, ret);
  sample_matrix_A_ff(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(seed_for_secret_and_error,
                                             prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____2 = sample_vector_cbd_then_ntt_e4(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
=======
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_340(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_ee0(uu____2, copy_of_prf_input0, 0U);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[2U];
  memcpy(
      error_as_ntt,
<<<<<<< HEAD
      sample_vector_cbd_then_ntt_e4(copy_of_prf_input, domain_separator).fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  compute_As_plus_e_ef(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[2U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A_transpose[2U]
                                                                        [2U];
  memcpy(copy_of_A_transpose, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 pk;
  memcpy(
      pk.t_as_ntt, copy_of_t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, copy_of_seed_for_A, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, copy_of_A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[2U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 sk;
  memcpy(
      sk.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_4c){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static void closure_1c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_20_1b(););
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 2
*/
static KRML_MUSTINLINE void H_a9_31(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_45(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  tuple_4c uu____0 = generate_keypair_unpacked_47(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, closure_1c(A[i]););
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_3a_33(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[2U][2U];
  memcpy(uu____2, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  uint8_t pk_serialized[800U];
  serialize_public_key_51(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_31(Eurydice_array_to_slice((size_t)800U, pk_serialized, uint8_t),
          public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U]);
  core_result_unwrap_41_33(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 uu____3 =
      ind_cpa_private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_implicit_rejection_value[32U];
  memcpy(copy_of_implicit_rejection_value, implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d6 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, copy_of_implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 uu____6 =
      ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_hash[32U];
  memcpy(copy_of_public_key_hash, public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, copy_of_public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  return lit;
=======
      sample_vector_cbd_then_ntt_out_7f0(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_a20(public_key->t_as_ntt, public_key->A,
                        private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
<<<<<<< HEAD
static libcrux_ml_kem_utils_extraction_helper_Keypair512 generate_keypair_93(
    Eurydice_slice key_generation_seed) {
  tuple_4c uu____0 = generate_keypair_unpacked_47(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 pk = uu____0.snd;
  uint8_t public_key_serialized[800U];
  serialize_public_key_51(
      pk.t_as_ntt, Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key_50(sk.secret_as_ntt, secret_key_serialized);
=======
static libcrux_ml_kem_utils_extraction_helper_Keypair512 generate_keypair_2f(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_d6 private_key = default_1a_190();
  IndCpaPublicKeyUnpacked_d6 public_key = default_8d_800();
  generate_keypair_unpacked_810(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[800U];
  serialize_public_key_020(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key_5f0(private_key.secret_as_ntt, secret_key_serialized);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[768U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[800U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
<<<<<<< HEAD
  libcrux_ml_kem_utils_extraction_helper_Keypair512 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  return result;
=======
  libcrux_ml_kem_utils_extraction_helper_Keypair512 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void serialize_kem_secret_key_eb(
=======
static KRML_MUSTINLINE void serialize_kem_secret_key_0a(
>>>>>>> main
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[1632U]) {
  uint8_t out[1632U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t);
  uint8_t ret0[32U];
<<<<<<< HEAD
  H_a9_31(public_key, ret0);
=======
  H_a9_160(public_key, ret0);
>>>>>>> main
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
  memcpy(ret, out, (size_t)1632U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
<<<<<<< HEAD
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_ind_cca_generate_keypair_f7(
=======
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_ind_cca_generate_keypair_51(
>>>>>>> main
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
<<<<<<< HEAD
      generate_keypair_93(ind_cpa_keypair_randomness);
=======
      generate_keypair_2f(ind_cpa_keypair_randomness);
>>>>>>> main
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
<<<<<<< HEAD
  serialize_kem_secret_key_eb(
=======
  serialize_kem_secret_key_0a(
>>>>>>> main
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1632U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_5e private_key =
<<<<<<< HEAD
      libcrux_ml_kem_types_from_e7_f1(copy_of_secret_key_serialized);
=======
      libcrux_ml_kem_types_from_88_2d(copy_of_secret_key_serialized);
>>>>>>> main
  libcrux_ml_kem_types_MlKemPrivateKey_5e uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[800U];
  memcpy(copy_of_public_key, public_key, (size_t)800U * sizeof(uint8_t));
<<<<<<< HEAD
  return libcrux_ml_kem_types_from_64_b1(
      uu____2, libcrux_ml_kem_types_from_07_a9(copy_of_public_key));
=======
  return libcrux_ml_kem_types_from_17_8b(
      uu____2, libcrux_ml_kem_types_from_40_60(copy_of_public_key));
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE void entropy_preprocess_d8_96(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 768
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_8c0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_1b(ring_element);
    deserialized_pk[i0] = uu____0;
  }
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_ef0(uint8_t (*input)[33U],
=======
static KRML_MUSTINLINE void PRFxN_081(uint8_t (*input)[33U],
>>>>>>> main
                                      uint8_t ret[2U][128U]) {
  uint8_t out[2U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t));
  uint8_t uu____0[128U];
  memcpy(uu____0, out0, (size_t)128U * sizeof(uint8_t));
  memcpy(out[0U], uu____0, (size_t)128U * sizeof(uint8_t));
  uint8_t uu____1[128U];
  memcpy(uu____1, out1, (size_t)128U * sizeof(uint8_t));
  memcpy(out[1U], uu____1, (size_t)128U * sizeof(uint8_t));
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_a9
with const generics
- K= 2
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRFxN_a9_410(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_ef0(input, ret);
=======
static KRML_MUSTINLINE void PRFxN_a9_161(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_081(input, ret);
>>>>>>> main
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_74
<<<<<<< HEAD
sample_ring_element_cbd_e7(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_20_1b(););
=======
sample_ring_element_cbd_c60(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_d6_7d(););
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[2U][128U];
<<<<<<< HEAD
  PRFxN_a9_410(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_8e0(
=======
  PRFxN_a9_161(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_af(
>>>>>>> main
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[2U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 result;
  memcpy(
<<<<<<< HEAD
      result.fst, copy_of_error_1,
=======
      lit.fst, copy_of_error_1,
>>>>>>> main
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 2
- LEN= 128
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_260(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_c90(input, ret);
=======
static KRML_MUSTINLINE void PRF_a9_422(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_d10(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void invert_ntt_montgomery_97(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_16(&zeta_i, re);
  invert_ntt_at_layer_2_88(&zeta_i, re);
  invert_ntt_at_layer_3_f7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_20_85(re);
=======
static KRML_MUSTINLINE void invert_ntt_montgomery_190(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_2b(&zeta_i, re);
  invert_ntt_at_layer_2_6a(&zeta_i, re);
  invert_ntt_at_layer_3_ad(&zeta_i, re);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_8f(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_2b(re);
>>>>>>> main
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void compute_vector_u_e3(
=======
static KRML_MUSTINLINE void compute_vector_u_ba0(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
<<<<<<< HEAD
                  result0[i] = ZERO_20_1b(););
=======
                  result[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)2U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
<<<<<<< HEAD
          ntt_multiply_20_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_20_47(&result0[i1], &product);
    }
    invert_ntt_montgomery_97(&result0[i1]);
    add_error_reduce_20_1f(&result0[i1], &error_1[i1]);
=======
          ntt_multiply_d6_f1(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_b80(&result[i1], &product);
    }
    invert_ntt_montgomery_190(&result[i1]);
    add_error_reduce_d6_89(&result[i1], &error_1[i1]);
>>>>>>> main
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U];
  memcpy(
      result, result0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_ring_element_v_e7(
=======
compute_ring_element_v_9f0(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
<<<<<<< HEAD
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_20_47(&result, &product););
  invert_ntt_montgomery_97(&result);
  result = add_message_error_reduce_20_69(error_2, message, result);
=======
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_b80(&result, &product););
  invert_ntt_montgomery_190(&result);
  result = add_message_error_reduce_d6_df(error_2, message, result);
>>>>>>> main
  return result;
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- OUT_LEN= 640
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
<<<<<<< HEAD
static void compress_then_serialize_u_9f(
=======
static void compress_then_serialize_u_0b0(
>>>>>>> main
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[2U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t);
    uint8_t ret[320U];
<<<<<<< HEAD
    compress_then_serialize_ring_element_u_81(&re, ret);
=======
    compress_then_serialize_ring_element_u_880(&re, ret);
>>>>>>> main
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_LEN= 640
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_unpacked_06(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_172(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____1 = sample_vector_cbd_then_ntt_e4(copy_of_prf_input0, 0U);
=======
static void encrypt_unpacked_be0(IndCpaPublicKeyUnpacked_d6 *public_key,
                                 uint8_t message[32U],
                                 Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____1 = sample_vector_cbd_then_ntt_out_7f0(copy_of_prf_input0, 0U);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____3 =
<<<<<<< HEAD
      sample_ring_element_cbd_e7(copy_of_prf_input, domain_separator0);
=======
      sample_ring_element_cbd_c60(copy_of_prf_input, domain_separator0);
>>>>>>> main
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
<<<<<<< HEAD
  PRF_a9_260(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_8e0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[2U];
  compute_vector_u_e3(public_key->A, r_as_ntt, error_1, u);
=======
  PRF_a9_422(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_af(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[2U];
  compute_vector_u_ba0(public_key->A, r_as_ntt, error_1, u);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
<<<<<<< HEAD
      deserialize_then_decompress_message_e3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_e7(public_key->t_as_ntt, r_as_ntt, &error_2,
                                &message_as_ring_element);
=======
      deserialize_then_decompress_message_ef(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_9f0(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
>>>>>>> main
  uint8_t ciphertext[768U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[2U];
  memcpy(
      uu____5, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
<<<<<<< HEAD
  compress_then_serialize_u_9f(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)640U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_0c(
=======
  compress_then_serialize_u_0b0(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)640U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_f30(
>>>>>>> main
      uu____6, Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                               (size_t)640U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

/**
<<<<<<< HEAD
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_ec libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_25(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  Eurydice_slice_copy(uu____0,
                      Eurydice_array_to_slice(
                          (size_t)32U, public_key->public_key_hash, uint8_t),
                      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____2 =
      &public_key->ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_unpacked_06(uu____2, copy_of_randomness, pseudorandomness,
                      ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 =
      libcrux_ml_kem_types_from_15_e9(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_ec lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.entropy_preprocess_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE void entropy_preprocess_af_15(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, randomness, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
}

/**
=======
>>>>>>> main
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_LEN= 640
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
static void encrypt_50(Eurydice_slice public_key, uint8_t message[32U],
                       Eurydice_slice randomness, uint8_t ret[768U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  deserialize_ring_elements_reduced_30(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t),
      t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)768U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_171(seed, ret0);
  sample_matrix_A_ff(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, seed_for_A);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_t_as_ntt[2U];
  memcpy(
      copy_of_t_as_ntt, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_A[2U][2U];
  memcpy(copy_of_A, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_for_A[32U];
  memcpy(copy_of_seed_for_A, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, copy_of_t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, copy_of_seed_for_A,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, copy_of_A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____3 =
      &public_key_unpacked;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[768U];
  encrypt_unpacked_06(uu____3, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)768U * sizeof(uint8_t));
=======
static void encrypt_a4(Eurydice_slice public_key, uint8_t message[32U],
                       Eurydice_slice randomness, uint8_t ret[768U]) {
  IndCpaPublicKeyUnpacked_d6 unpacked_public_key = default_8d_800();
  deserialize_ring_elements_reduced_8c0(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)768U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[2U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_340(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_d6 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[768U];
  encrypt_unpacked_be0(uu____1, copy_of_message, randomness, ret1);
  memcpy(ret, ret1, (size_t)768U * sizeof(uint8_t));
>>>>>>> main
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void kdf_af_6e(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, shared_secret, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_33(dst, ret);
=======
static KRML_MUSTINLINE void kdf_d8_e9(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
<<<<<<< HEAD
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_b3(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_15(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_9c(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_96(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
<<<<<<< HEAD
  H_a9_31(Eurydice_array_to_slice(
              (size_t)800U, libcrux_ml_kem_types_as_slice_f6_ae(public_key),
              uint8_t),
          ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_ab(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
=======
  H_a9_160(Eurydice_array_to_slice(
               (size_t)800U, libcrux_ml_kem_types_as_slice_ba_120(public_key),
               uint8_t),
           ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_670(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
<<<<<<< HEAD
      (size_t)800U, libcrux_ml_kem_types_as_slice_f6_ae(public_key), uint8_t);
=======
      (size_t)800U, libcrux_ml_kem_types_as_slice_ba_120(public_key), uint8_t);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
<<<<<<< HEAD
  encrypt_50(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
=======
  encrypt_a4(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
>>>>>>> main
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 ciphertext0 =
<<<<<<< HEAD
      libcrux_ml_kem_types_from_15_e9(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_af_6e(shared_secret, shared_secret_array);
=======
      libcrux_ml_kem_types_from_fc_360(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_e9(shared_secret, shared_secret_array);
>>>>>>> main
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
<<<<<<< HEAD
  tuple_ec result;
  result.fst = uu____5;
  memcpy(result.snd, copy_of_shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  return result;
=======
  tuple_ec lit;
  lit.fst = uu____5;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
>>>>>>> main
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_secret_key_c5(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_d6_7d(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_71(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void deserialize_then_decompress_u_4a(
=======
static KRML_MUSTINLINE void deserialize_then_decompress_u_9d0(
>>>>>>> main
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
<<<<<<< HEAD
                  u_as_ntt[i] = ZERO_20_1b(););
=======
                  u_as_ntt[i] = ZERO_d6_7d(););
>>>>>>> main
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)768U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice2(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t);
<<<<<<< HEAD
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_d5(u_bytes);
    ntt_vector_u_27(&u_as_ntt[i0]);
=======
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_f90(u_bytes);
    ntt_vector_u_9b0(&u_as_ntt[i0]);
>>>>>>> main
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
<<<<<<< HEAD
compute_message_3f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_20_1b();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_20_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_20_47(&result, &product););
  invert_ntt_montgomery_97(&result);
  result = subtract_reduce_20_8c(v, result);
=======
compute_message_6a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_d6_7d();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_d6_f1(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_b80(&result, &product););
  invert_ntt_montgomery_190(&result);
  result = subtract_reduce_d6_4a(v, result);
>>>>>>> main
  return result;
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
<<<<<<< HEAD
static void decrypt_unpacked_4c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  deserialize_then_decompress_u_4a(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_08(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_3f(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_2d(message, ret0);
=======
static void decrypt_unpacked_670(IndCpaPrivateKeyUnpacked_d6 *secret_key,
                                 uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  deserialize_then_decompress_u_9d0(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_590(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_6a0(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_53(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_3d(Eurydice_slice secret_key, uint8_t *ciphertext,
                       uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  deserialize_secret_key_c5(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[2U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_d6 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_670(&secret_key_unpacked, ciphertext, ret0);
>>>>>>> main
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_a9
with const generics
- K= 2
- LEN= 32
*/
<<<<<<< HEAD
static KRML_MUSTINLINE void PRF_a9_26(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_c9(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_d6(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6 *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_4c(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_a9_ab(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_170(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_ba_ff(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_26(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
            implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_unpacked_06(uu____3, copy_of_decrypted, pseudorandomness,
                      expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_ba_ff(ciphertext),
          Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_secret_key_88(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_20_1b(););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(secret_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_ae(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U];
  memcpy(
      result, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_d2(Eurydice_slice secret_key, uint8_t *ciphertext,
                       uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  deserialize_secret_key_88(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[2U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_4c(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
=======
static KRML_MUSTINLINE void PRF_a9_421(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_d1(input, ret);
>>>>>>> main
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 800
*/
<<<<<<< HEAD
void libcrux_ml_kem_ind_cca_decapsulate_e2(
=======
void libcrux_ml_kem_ind_cca_decapsulate_97(
>>>>>>> main
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t),
      (size_t)768U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)800U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
<<<<<<< HEAD
  decrypt_d2(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_17(
=======
  decrypt_3d(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
>>>>>>> main
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
<<<<<<< HEAD
  G_a9_ab(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
=======
  G_a9_670(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
>>>>>>> main
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[800U];
<<<<<<< HEAD
  libcrux_ml_kem_utils_into_padded_array_170(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_ba_ff(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_26(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
=======
  libcrux_ml_kem_utils_into_padded_array_424(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_fd_ed0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_421(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
             implicit_rejection_shared_secret0);
>>>>>>> main
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
<<<<<<< HEAD
  encrypt_50(uu____5, copy_of_decrypted, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_6e(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_af_6e(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_ba_ff(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
=======
  encrypt_a4(uu____5, copy_of_decrypted, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_e9(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_e9(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_fd_ed0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
>>>>>>> main
}
