/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 650b216aeb5901ec6f1c44ff275acd924e54bdbd
 * Libcrux: b1ecb428c60dd375b8bdd05c258cd0e4d5f1fec1
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_vec_zero(void) {
  return mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ZERO_09(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array) {
  return mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
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
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_to_i16_array_09(__m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_vec_to_i16_array(x, ret);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
__m256i libcrux_ml_kem_vector_avx2_add_09(__m256i lhs, __m256i *rhs) {
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
__m256i libcrux_ml_kem_vector_avx2_sub_09(__m256i lhs, __m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(__m256i vector,
                                                           int16_t constant) {
  __m256i cv = mm256_set1_epi16(constant);
  return mm256_mullo_epi16(vector, cv);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
__m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_09(__m256i vec,
                                                           int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(vec, c);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant) {
  __m256i cv = mm256_set1_epi16(constant);
  return mm256_and_si256(vector, cv);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
__m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
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
__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_09(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i vector) {
  __m256i t0 = mm256_mulhi_epi16(
      vector, mm256_set1_epi16(
                  LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  __m256i t1 = mm256_add_epi16(t0, mm256_set1_epi16((int16_t)512));
  __m256i quotient = mm256_srai_epi16((int32_t)10, t1, __m256i);
  __m256i quotient_times_field_modulus = mm256_mullo_epi16(
      quotient, mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return mm256_sub_epi16(vector, quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
__m256i libcrux_ml_kem_vector_avx2_barrett_reduce_09(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i vector, int16_t constant) {
  __m256i vec_constant = mm256_set1_epi16(constant);
  __m256i value_low = mm256_mullo_epi16(vector, vec_constant);
  __m256i k = mm256_mullo_epi16(
      value_low,
      mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus = mm256_mulhi_epi16(k, modulus);
  __m256i value_high = mm256_mulhi_epi16(vector, vec_constant);
  return mm256_sub_epi16(value_high, k_times_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
__m256i libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
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
__m256i libcrux_ml_kem_vector_avx2_compress_1_09(__m256i vector) {
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
    __m256i vec, __m256i constants) {
  __m256i value_low = mm256_mullo_epi16(vec, constants);
  __m256i k = mm256_mullo_epi16(
      value_low,
      mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i modulus =
      mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus = mm256_mulhi_epi16(k, modulus);
  __m256i value_high = mm256_mulhi_epi16(vec, constants);
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
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_09(__m256i vector,
                                                       int16_t zeta0,
                                                       int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_MUSTINLINE __m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    __m128i vec, __m128i constants) {
  __m128i value_low = mm_mullo_epi16(vec, constants);
  __m128i k = mm_mullo_epi16(
      value_low,
      mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m128i modulus = mm_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m128i k_times_modulus = mm_mulhi_epi16(k, modulus);
  __m128i value_high = mm_mulhi_epi16(vec, constants);
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
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_09(__m256i vector,
                                                           int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(__m256i vec) {
  __m256i k = mm256_mullo_epi16(
      vec,
      mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = mm256_mulhi_epi16(
      k, mm256_set1_epi32((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high = mm256_srli_epi32((int32_t)16, vec, __m256i);
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
__m256i libcrux_ml_kem_vector_avx2_ntt_multiply_09(__m256i *lhs, __m256i *rhs,
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
  ret[0U] = (uint8_t)bits_packed;
  ret[1U] = (uint8_t)(bits_packed >> 8U);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_serialize_1_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_1_09(Eurydice_slice bytes) {
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
  core_result_unwrap_26_0e(dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_serialize_4_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_4_09(Eurydice_slice bytes) {
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
  core_result_unwrap_26_07(dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_serialize_5_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_5_09(Eurydice_slice bytes) {
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
  core_result_unwrap_26_ea(dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_serialize_10_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_10_09(Eurydice_slice bytes) {
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
void libcrux_ml_kem_vector_avx2_serialize_11_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_11_09(Eurydice_slice bytes) {
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
  core_result_unwrap_26_76(dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
void libcrux_ml_kem_vector_avx2_serialize_12_09(__m256i vector,
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
__m256i libcrux_ml_kem_vector_avx2_deserialize_12_09(Eurydice_slice bytes) {
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
inline __m256i libcrux_ml_kem_vector_avx2_clone_78(__m256i *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ZERO_ef_05(void) {
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
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_reduced_ring_element_dc(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_09(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_cond_subtract_3329_09(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_531(
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
        deserialize_to_reduced_ring_element_dc(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_cc1(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_05(););
  deserialize_ring_elements_reduced_531(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE __m256i shift_right_65(__m256i vector) {
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
static __m256i shift_right_09_85(__m256i vector) {
  return shift_right_65(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static __m256i to_unsigned_representative_3f(__m256i a) {
  __m256i t = shift_right_09_85(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_09(a, &fm);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i to_unsigned_field_modulus_7b(__m256i a) {
  return to_unsigned_representative_3f(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_2c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = to_unsigned_field_modulus_7b(re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2_serialize_12_09(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)24U * i0, (size_t)24U * i0 + (size_t)24U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)24U, bytes, uint8_t), uint8_t);
  }
  uint8_t result[384U];
  memcpy(result, serialized, (size_t)384U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)384U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 1152
*/
static KRML_MUSTINLINE void serialize_secret_key_991(
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
    serialize_uncompressed_ring_element_2c(&re, ret0);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)1152U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_6c1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)1152U, uint8_t);
  uint8_t ret[1152U];
  serialize_secret_key_991(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1152U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1184U, serialized, (size_t)1152U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_ca1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  serialize_public_key_mut_6c1(t_as_ntt, seed_for_a, public_key_serialized);
  uint8_t result[1184U];
  memcpy(result, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)1184U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_521(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  deserialize_ring_elements_reduced_out_cc1(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_ca1(
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
static KRML_MUSTINLINE void H_a9_411(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_701(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  uint8_t t[32U];
  H_a9_411(Eurydice_array_to_subslice2(
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
static IndCpaPrivateKeyUnpacked_a0 default_1a_3c1(void) {
  IndCpaPrivateKeyUnpacked_a0 lit;
  lit.secret_as_ntt[0U] = ZERO_ef_05();
  lit.secret_as_ntt[1U] = ZERO_ef_05();
  lit.secret_as_ntt[2U] = ZERO_ef_05();
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
static IndCpaPublicKeyUnpacked_a0 default_8d_891(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  uu____0[i] = ZERO_ef_05(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_ef_05();
  lit.A[0U][1U] = ZERO_ef_05();
  lit.A[0U][2U] = ZERO_ef_05();
  lit.A[1U][0U] = ZERO_ef_05();
  lit.A[1U][1U] = ZERO_ef_05();
  lit.A[1U][2U] = ZERO_ef_05();
  lit.A[2U][0U] = ZERO_ef_05();
  lit.A[2U][1U] = ZERO_ef_05();
  lit.A[2U][2U] = ZERO_ef_05();
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
static KRML_MUSTINLINE void G_a9_9f1(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_751(
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
  G_a9_9f1(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_961(uint8_t input[3U][34U]) {
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
shake128_init_absorb_final_a9_c11(uint8_t input[3U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[3U][34U];
  memcpy(copy_of_input, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_961(copy_of_input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_081(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_7a1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_first_three_blocks_081(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe3(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_011(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_9f1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_next_block_011(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe4(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
from_i16_array_ef_ef(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_from_i16_array_09(Eurydice_slice_subslice2(
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_b41(
    int16_t s[272U]) {
  return from_i16_array_ef_ef(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_901(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[3U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_c11(copy_of_seeds);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_first_three_blocks_a9_7a1(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[3U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_fe3(
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      shake128_squeeze_next_block_a9_9f1(&xof_state, randomness);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[3U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)3U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_fe4(
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = closure_b41(copy_of_out[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_ee1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[3U],
    uint8_t seed[34U], bool transpose) {
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
      sample_from_xof_901(copy_of_seeds, sampled);
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
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_fb2(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_b22(uint8_t (*input)[33U],
                                         uint8_t ret[3U][128U]) {
  PRFxN_fb2(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_2_4a(Eurydice_slice randomness) {
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
  return from_i16_array_ef_ef(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_3_20(Eurydice_slice randomness) {
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
  return from_i16_array_ef_ef(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_d7(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_4a(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_13(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_09(
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
static __m256i montgomery_multiply_fe_5f(__m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
ntt_layer_int_vec_step_97(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i t = montgomery_multiply_fe_5f(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_09(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_09(a, &t);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_ca(
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
          ntt_layer_int_vec_step_97(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]));
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
static KRML_MUSTINLINE void ntt_at_layer_3_ba(
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
static KRML_MUSTINLINE void ntt_at_layer_2_89(
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
static KRML_MUSTINLINE void ntt_at_layer_1_d7(
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_ef_a9(
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
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_ef(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  ntt_at_layer_7_13(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ba(&zeta_i, re);
  ntt_at_layer_2_89(&zeta_i, re);
  ntt_at_layer_1_d7(&zeta_i, re);
  poly_barrett_reduce_ef_a9(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b01(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
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
  PRFxN_a9_b22(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_d7(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ef(&re_as_ntt[i0]););
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
static KRML_MUSTINLINE tuple_b0 sample_vector_cbd_then_ntt_out_811(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  re_as_ntt[i] = ZERO_ef_05(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_b01(uu____0, uu____1, domain_separator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[3U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b0 result;
  memcpy(
      result.fst, copy_of_re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
ntt_multiply_ef_b2(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out = ZERO_ef_05();
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
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_ef_4f1(
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
static __m256i to_standard_domain_79(__m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_ef_34(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        to_standard_domain_79(self->coefficients[j]);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_2d1(
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_ef_05();
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
          ntt_multiply_ef_b2(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_4f1(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_34(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void generate_keypair_unpacked_a41(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_a0 *private_key,
    IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_751(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_ee1(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b01(uu____2, copy_of_prf_input0, 0U);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_out_811(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_2d1(public_key->t_as_ntt, public_key->A,
                        private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
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
static libcrux_ml_kem_utils_extraction_helper_Keypair768 generate_keypair_6a1(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_a0 private_key = default_1a_3c1();
  IndCpaPublicKeyUnpacked_a0 public_key = default_8d_891();
  generate_keypair_unpacked_a41(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1184U];
  serialize_public_key_ca1(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key_991(private_key.secret_as_ntt, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1152U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1184U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair768 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_1f1(
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
  H_a9_411(public_key, ret0);
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
libcrux_ml_kem_ind_cca_generate_keypair_0b1(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_6a1(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key_1f1(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_7f_af0(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_ee0(
      uu____2, libcrux_ml_kem_types_from_5a_670(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_641(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_b0
sample_ring_element_cbd_a01(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_ef_05(););
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
  PRFxN_a9_b22(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_d7(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[3U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b0 result;
  memcpy(
      result.fst, copy_of_error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_960(Eurydice_slice input, uint8_t ret[128U]) {
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
static KRML_MUSTINLINE void PRF_a9_164(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_960(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_f7(
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
static KRML_MUSTINLINE void invert_ntt_at_layer_2_98(
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
static KRML_MUSTINLINE void invert_ntt_at_layer_3_fe(
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
inv_ntt_layer_int_vec_step_reduce_75(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_09(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
      libcrux_ml_kem_vector_avx2_add_09(a, &b));
  b = montgomery_multiply_fe_5f(a_minus_b, zeta_r);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_bc(
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
          inv_ntt_layer_int_vec_step_reduce_75(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_get_zeta(zeta_i[0U]));
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
static KRML_MUSTINLINE void invert_ntt_montgomery_8f1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_f7(&zeta_i, re);
  invert_ntt_at_layer_2_98(&zeta_i, re);
  invert_ntt_at_layer_3_fe(&zeta_i, re);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_a9(re);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_ef_dd(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
            self->coefficients[j], (int16_t)1441);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_dd1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result0[i] = ZERO_ef_05(););
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
          ntt_multiply_ef_b2(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_4f1(&result0[i1], &product);
    }
    invert_ntt_montgomery_8f1(&result0[i1]);
    add_error_reduce_ef_dd(&result0[i1], &error_1[i1]);
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
static __m256i decompress_1_08(__m256i vec) {
  __m256i z = libcrux_ml_kem_vector_avx2_ZERO_09();
  __m256i s = libcrux_ml_kem_vector_avx2_sub_09(z, &vec);
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(s,
                                                                 (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_message_d3(uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_deserialize_1_09(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t));
      re.coefficients[i0] = decompress_1_08(coefficient_compressed););
  return re;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
add_message_error_reduce_ef_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
            result.coefficients[i0], (int16_t)1441);
    __m256i tmp = libcrux_ml_kem_vector_avx2_add_09(self->coefficients[i0],
                                                    &message->coefficients[i0]);
    __m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_09(coefficient_normal_form, &tmp);
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_09(tmp0);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_ring_element_v_771(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_4f1(&result, &product););
  invert_ntt_montgomery_8f1(&result);
  result = add_message_error_reduce_ef_79(error_2, message, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
compress_ciphertext_coefficient_43(__m256i vector) {
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
static __m256i compress_09_76(__m256i vector) {
  return compress_ciphertext_coefficient_43(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_2b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_09_76(to_unsigned_field_modulus_7b(re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2_serialize_10_09(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)20U * i0, (size_t)20U * i0 + (size_t)20U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)20U, bytes, uint8_t), uint8_t);
  }
  uint8_t result[320U];
  memcpy(result, serialized, (size_t)320U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i
compress_ciphertext_coefficient_430(__m256i vector) {
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
static __m256i compress_09_760(__m256i vector) {
  return compress_ciphertext_coefficient_430(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_9e0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_2b0(re, uu____0);
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static void compress_then_serialize_u_421(
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
    compress_then_serialize_ring_element_u_9e0(&re, ret);
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
compress_ciphertext_coefficient_431(__m256i vector) {
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
static __m256i compress_09_761(__m256i vector) {
  return compress_ciphertext_coefficient_431(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_a4(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_09_761(to_unsigned_field_modulus_7b(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_09(coefficient, bytes);
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
compress_ciphertext_coefficient_432(__m256i vector) {
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
static __m256i compress_09_762(__m256i vector) {
  return compress_ciphertext_coefficient_432(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_03(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficients =
        compress_09_762(to_unsigned_representative_3f(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_09(coefficients, bytes);
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
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_d10(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_4_a4(re, out);
}

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
static void encrypt_unpacked_a41(IndCpaPublicKeyUnpacked_a0 *public_key,
                                 uint8_t message[32U],
                                 Eurydice_slice randomness,
                                 uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b0 uu____1 = sample_vector_cbd_then_ntt_out_811(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b0 uu____3 =
      sample_ring_element_cbd_a01(copy_of_prf_input, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_164(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_d7(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  compute_vector_u_dd1(public_key->A, r_as_ntt, error_1, u);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_d3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_771(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_421(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_d10(
      uu____6, Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                               (size_t)960U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
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
static void encrypt_6f1(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1088U]) {
  IndCpaPublicKeyUnpacked_a0 unpacked_public_key = default_8d_891();
  deserialize_ring_elements_reduced_531(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[3U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_ee1(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_a0 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[1088U];
  encrypt_unpacked_a41(uu____1, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)1088U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_161(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_a11(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_641(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  H_a9_411(Eurydice_array_to_slice(
               (size_t)1184U, libcrux_ml_kem_types_as_slice_fd_fe1(public_key),
               uint8_t),
           ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_9f1(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_fd_fe1(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_6f1(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_01_451(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_161(shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
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
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_uncompressed_ring_element_6c(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
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
static KRML_MUSTINLINE void deserialize_secret_key_541(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_ef_05(););
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
        deserialize_to_uncompressed_ring_element_6c(secret_bytes);
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
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_79(__m256i vector) {
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
static __m256i decompress_ciphertext_coefficient_09_c6(__m256i vector) {
  return decompress_ciphertext_coefficient_79(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_10_c7(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  LowStar_Ignore_ignore(
      Eurydice_slice_len(
          Eurydice_array_to_slice((size_t)16U, re.coefficients, __m256i),
          __m256i),
      size_t, void *);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_c6(coefficient);
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
decompress_ciphertext_coefficient_790(__m256i vector) {
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
static __m256i decompress_ciphertext_coefficient_09_c60(__m256i vector) {
  return decompress_ciphertext_coefficient_790(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_11_d5(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_c60(coefficient);
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
deserialize_then_decompress_ring_element_u_790(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_c7(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_b70(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ba(&zeta_i, re);
  ntt_at_layer_2_89(&zeta_i, re);
  ntt_at_layer_1_d7(&zeta_i, re);
  poly_barrett_reduce_ef_a9(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_251(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_05(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_790(u_bytes);
    ntt_vector_u_b70(&u_as_ntt[i0]);
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
decompress_ciphertext_coefficient_791(__m256i vector) {
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
static __m256i decompress_ciphertext_coefficient_09_c61(__m256i vector) {
  return decompress_ciphertext_coefficient_791(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_4_75(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_09(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_09_c61(coefficient);
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
decompress_ciphertext_coefficient_792(__m256i vector) {
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
static __m256i decompress_ciphertext_coefficient_09_c62(__m256i vector) {
  return decompress_ciphertext_coefficient_792(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_5_f8(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_ef_05();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_09(bytes);
    re.coefficients[i0] =
        decompress_ciphertext_coefficient_09_c62(re.coefficients[i0]);
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
deserialize_then_decompress_ring_element_v_b90(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_75(serialized);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
subtract_reduce_ef_da(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
            b.coefficients[i0], (int16_t)1441);
    b.coefficients[i0] = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
        libcrux_ml_kem_vector_avx2_sub_09(self->coefficients[i0],
                                          &coefficient_normal_form));
  }
  return b;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_message_7d1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_4f1(&result, &product););
  invert_ntt_montgomery_8f1(&result);
  result = subtract_reduce_ef_da(v, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_dd(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient = to_unsigned_field_modulus_7b(re.coefficients[i0]);
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_09(coefficient);
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_avx2_serialize_1_09(coefficient_compressed, bytes);
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          serialized, (size_t)2U * i0, (size_t)2U * i0 + (size_t)2U, uint8_t);
      Eurydice_slice_copy(uu____0,
                          Eurydice_array_to_slice((size_t)2U, bytes, uint8_t),
                          uint8_t););
  uint8_t result[32U];
  memcpy(result, serialized, (size_t)32U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
}

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
static void decrypt_unpacked_9d1(IndCpaPrivateKeyUnpacked_a0 *secret_key,
                                 uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  deserialize_then_decompress_u_251(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_b90(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_7d1(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_dd(message, ret0);
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
static void decrypt_751(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  deserialize_secret_key_541(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[3U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_a0 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_9d1(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_96(Eurydice_slice input, uint8_t ret[32U]) {
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
static KRML_MUSTINLINE void PRF_a9_163(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_96(input, ret);
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
void libcrux_ml_kem_ind_cca_decapsulate_7f1(
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
  decrypt_751(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_9f1(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_425(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_00_401(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_163(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
             implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_6f1(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_161(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_d8_161(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_401(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_53(
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
        deserialize_to_reduced_ring_element_dc(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_cc0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_05(););
  deserialize_ring_elements_reduced_53(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- OUT_LEN= 1536
*/
static KRML_MUSTINLINE void serialize_secret_key_99(
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
    serialize_uncompressed_ring_element_2c(&re, ret0);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)1536U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)1536U, uint8_t);
  uint8_t ret[1536U];
  serialize_secret_key_99(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1536U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1568U, serialized, (size_t)1536U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_ca(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  serialize_public_key_mut_6c(t_as_ntt, seed_for_a, public_key_serialized);
  uint8_t result[1568U];
  memcpy(result, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)1568U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_520(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  deserialize_ring_elements_reduced_out_cc0(
      Eurydice_array_to_subslice_to((size_t)1568U, public_key, (size_t)1536U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_ca(
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
static KRML_MUSTINLINE void H_a9_41(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_700(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *_ciphertext) {
  uint8_t t[32U];
  H_a9_41(Eurydice_array_to_subslice2(
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
static IndCpaPrivateKeyUnpacked_01 default_1a_3c(void) {
  IndCpaPrivateKeyUnpacked_01 lit;
  lit.secret_as_ntt[0U] = ZERO_ef_05();
  lit.secret_as_ntt[1U] = ZERO_ef_05();
  lit.secret_as_ntt[2U] = ZERO_ef_05();
  lit.secret_as_ntt[3U] = ZERO_ef_05();
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
static IndCpaPublicKeyUnpacked_01 default_8d_89(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  uu____0[i] = ZERO_ef_05(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_01 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_ef_05();
  lit.A[0U][1U] = ZERO_ef_05();
  lit.A[0U][2U] = ZERO_ef_05();
  lit.A[0U][3U] = ZERO_ef_05();
  lit.A[1U][0U] = ZERO_ef_05();
  lit.A[1U][1U] = ZERO_ef_05();
  lit.A[1U][2U] = ZERO_ef_05();
  lit.A[1U][3U] = ZERO_ef_05();
  lit.A[2U][0U] = ZERO_ef_05();
  lit.A[2U][1U] = ZERO_ef_05();
  lit.A[2U][2U] = ZERO_ef_05();
  lit.A[2U][3U] = ZERO_ef_05();
  lit.A[3U][0U] = ZERO_ef_05();
  lit.A[3U][1U] = ZERO_ef_05();
  lit.A[3U][2U] = ZERO_ef_05();
  lit.A[3U][3U] = ZERO_ef_05();
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
static KRML_MUSTINLINE void G_a9_9f(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_75(
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
  G_a9_9f(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_96(uint8_t input[4U][34U]) {
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
shake128_init_absorb_final_a9_c1(uint8_t input[4U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[4U][34U];
  memcpy(copy_of_input, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_96(copy_of_input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_08(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_7a(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_first_three_blocks_08(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_01(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_9f(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_next_block_01(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe0(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_b4(
    int16_t s[272U]) {
  return from_i16_array_ef_ef(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_90(
    uint8_t seeds[4U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[4U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)4U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_c1(copy_of_seeds);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_first_three_blocks_a9_7a(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[4U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_fe(
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      shake128_squeeze_next_block_a9_9f(&xof_state, randomness);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[4U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)4U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_fe0(
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[4U][272U];
  memcpy(copy_of_out, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = closure_b4(copy_of_out[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_ee(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[4U],
    uint8_t seed[34U], bool transpose) {
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
      sample_from_xof_90(copy_of_seeds, sampled);
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
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_fb(uint8_t (*input)[33U],
                                     uint8_t ret[4U][128U]) {
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
static KRML_MUSTINLINE void PRFxN_a9_b2(uint8_t (*input)[33U],
                                        uint8_t ret[4U][128U]) {
  PRFxN_fb(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
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
  PRFxN_a9_b2(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_d7(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ef(&re_as_ntt[i0]););
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
static KRML_MUSTINLINE tuple_71 sample_vector_cbd_then_ntt_out_81(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  re_as_ntt[i] = ZERO_ef_05(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_b0(uu____0, uu____1, domain_separator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[4U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 result;
  memcpy(
      result.fst, copy_of_re_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_ef_4f(
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
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_2d(
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_ef_05();
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
          ntt_multiply_ef_b2(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_4f(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_34(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void generate_keypair_unpacked_a4(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_01 *private_key,
    IndCpaPublicKeyUnpacked_01 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_75(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[4U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_ee(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b0(uu____2, copy_of_prf_input0, 0U);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[4U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_out_81(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_2d(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
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
static libcrux_ml_kem_utils_extraction_helper_Keypair1024 generate_keypair_6a0(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_01 private_key = default_1a_3c();
  IndCpaPublicKeyUnpacked_01 public_key = default_8d_89();
  generate_keypair_unpacked_a4(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1568U];
  serialize_public_key_ca(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key_99(private_key.secret_as_ntt, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1536U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1568U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_1f0(
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
  H_a9_41(public_key, ret0);
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
libcrux_ml_kem_ind_cca_generate_keypair_0b0(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_6a0(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key_1f0(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[3168U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_95 private_key =
      libcrux_ml_kem_types_from_7f_af1(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_95 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1568U];
  memcpy(copy_of_public_key, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_ee1(
      uu____2, libcrux_ml_kem_types_from_5a_671(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_640(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_71
sample_ring_element_cbd_a0(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_ef_05(););
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
  PRFxN_a9_b2(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_d7(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[4U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 result;
  memcpy(
      result.fst, copy_of_error_1,
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
static KRML_MUSTINLINE void PRF_a9_160(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_960(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_8f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_f7(&zeta_i, re);
  invert_ntt_at_layer_2_98(&zeta_i, re);
  invert_ntt_at_layer_3_fe(&zeta_i, re);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_a9(re);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_dd(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result0[i] = ZERO_ef_05(););
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
          ntt_multiply_ef_b2(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_4f(&result0[i1], &product);
    }
    invert_ntt_montgomery_8f(&result0[i1]);
    add_error_reduce_ef_dd(&result0[i1], &error_1[i1]);
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
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_ring_element_v_77(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_4f(&result, &product););
  invert_ntt_montgomery_8f(&result);
  result = add_message_error_reduce_ef_79(error_2, message, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_17(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_09_760(to_unsigned_representative_3f(re->coefficients[i0]));
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
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_9e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_17(re, uu____0);
  memcpy(ret, uu____0, (size_t)352U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- OUT_LEN= 1408
- COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static void compress_then_serialize_u_42(
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
    compress_then_serialize_ring_element_u_9e(&re, ret);
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
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_d1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_5_03(re, out);
}

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
static void encrypt_unpacked_a4(IndCpaPublicKeyUnpacked_01 *public_key,
                                uint8_t message[32U], Eurydice_slice randomness,
                                uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____1 = sample_vector_cbd_then_ntt_out_81(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____3 =
      sample_ring_element_cbd_a0(copy_of_prf_input, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_160(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_d7(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[4U];
  compute_vector_u_dd(public_key->A, r_as_ntt, error_1, u);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_d3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_77(public_key->t_as_ntt, r_as_ntt, &error_2,
                                &message_as_ring_element);
  uint8_t ciphertext[1568U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[4U];
  memcpy(
      uu____5, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_42(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                           (size_t)1408U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_d1(
      uu____6, Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                               (size_t)1408U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

/**
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
static void encrypt_6f0(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1568U]) {
  IndCpaPublicKeyUnpacked_01 unpacked_public_key = default_8d_89();
  deserialize_ring_elements_reduced_53(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1536U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[4U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_ee(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_01 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[1568U];
  encrypt_unpacked_a4(uu____1, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)1568U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_160(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_a10(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_640(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  H_a9_41(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_fd_fe(public_key),
              uint8_t),
          ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_9f(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_fd_fe(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_6f0(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_1f ciphertext0 =
      libcrux_ml_kem_types_from_01_45(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_160(shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext_1f uu____5 = ciphertext0;
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_secret_key_540(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_ef_05(););
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
        deserialize_to_uncompressed_ring_element_6c(secret_bytes);
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
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_ring_element_u_79(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_d5(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_b7(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ca(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ba(&zeta_i, re);
  ntt_at_layer_2_89(&zeta_i, re);
  ntt_at_layer_1_d7(&zeta_i, re);
  poly_barrett_reduce_ef_a9(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_25(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_05(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_79(u_bytes);
    ntt_vector_u_b7(&u_as_ntt[i0]);
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
deserialize_then_decompress_ring_element_v_b9(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_f8(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_message_7d(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_4f(&result, &product););
  invert_ntt_montgomery_8f(&result);
  result = subtract_reduce_ef_da(v, result);
  return result;
}

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
static void decrypt_unpacked_9d(IndCpaPrivateKeyUnpacked_01 *secret_key,
                                uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  deserialize_then_decompress_u_25(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_b9(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_7d(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_dd(message, ret0);
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
static void decrypt_750(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  deserialize_secret_key_540(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[4U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_01 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_9d(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void PRF_a9_16(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_96(input, ret);
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
void libcrux_ml_kem_ind_cca_decapsulate_7f0(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *ciphertext, uint8_t ret[32U]) {
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
  decrypt_750(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_9f(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_420(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_00_40(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_16(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_6f0(uu____5, copy_of_decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_160(Eurydice_array_to_slice(
                 (size_t)32U, implicit_rejection_shared_secret0, uint8_t),
             implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_d8_160(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_40(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_530(
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
        deserialize_to_reduced_ring_element_dc(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_cc(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_05(););
  deserialize_ring_elements_reduced_530(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- OUT_LEN= 768
*/
static KRML_MUSTINLINE void serialize_secret_key_990(
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
    serialize_uncompressed_ring_element_2c(&re, ret0);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)768U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_mut_6c0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)768U, uint8_t);
  uint8_t ret[768U];
  serialize_secret_key_990(t_as_ntt, ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)768U, ret, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)800U, serialized, (size_t)768U,
                                      uint8_t, size_t),
      seed_for_a, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_ca0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  serialize_public_key_mut_6c0(t_as_ntt, seed_for_a, public_key_serialized);
  uint8_t result[800U];
  memcpy(result, public_key_serialized, (size_t)800U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)800U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_52(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  deserialize_ring_elements_reduced_out_cc(
      Eurydice_array_to_subslice_to((size_t)800U, public_key, (size_t)768U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key_ca0(
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
static KRML_MUSTINLINE void H_a9_410(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_70(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *_ciphertext) {
  uint8_t t[32U];
  H_a9_410(Eurydice_array_to_subslice2(
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
static IndCpaPrivateKeyUnpacked_d6 default_1a_3c0(void) {
  IndCpaPrivateKeyUnpacked_d6 lit;
  lit.secret_as_ntt[0U] = ZERO_ef_05();
  lit.secret_as_ntt[1U] = ZERO_ef_05();
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
static IndCpaPublicKeyUnpacked_d6 default_8d_890(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  uu____0[i] = ZERO_ef_05(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_d6 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = ZERO_ef_05();
  lit.A[0U][1U] = ZERO_ef_05();
  lit.A[1U][0U] = ZERO_ef_05();
  lit.A[1U][1U] = ZERO_ef_05();
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
static KRML_MUSTINLINE void G_a9_9f0(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_750(
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
  G_a9_9f0(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_960(uint8_t input[2U][34U]) {
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
shake128_init_absorb_final_a9_c10(uint8_t input[2U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[2U][34U];
  memcpy(copy_of_input, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_960(copy_of_input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_080(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_7a0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_first_three_blocks_080(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe1(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_010(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_9f0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_next_block_010(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_fe2(
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_b40(
    int16_t s[272U]) {
  return from_i16_array_ef_ef(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_from_xof_900(
    uint8_t seeds[2U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[2U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)2U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_c10(copy_of_seeds);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_first_three_blocks_a9_7a0(&xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[2U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_fe1(
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      shake128_squeeze_next_block_a9_9f0(&xof_state, randomness);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[2U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)2U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_fe2(
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[2U][272U];
  memcpy(copy_of_out, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = closure_b40(copy_of_out[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_ee0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[2U],
    uint8_t seed[34U], bool transpose) {
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
      sample_from_xof_900(copy_of_seeds, sampled);
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
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_fb0(uint8_t (*input)[33U],
                                      uint8_t ret[2U][192U]) {
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
static KRML_MUSTINLINE void PRFxN_a9_b20(uint8_t (*input)[33U],
                                         uint8_t ret[2U][192U]) {
  PRFxN_fb0(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_d70(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_20(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
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
  PRFxN_a9_b20(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_d70(
          Eurydice_array_to_slice((size_t)192U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ef(&re_as_ntt[i0]););
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
static KRML_MUSTINLINE tuple_74 sample_vector_cbd_then_ntt_out_810(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  re_as_ntt[i] = ZERO_ef_05(););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator =
      sample_vector_cbd_then_ntt_b00(uu____0, uu____1, domain_separator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[2U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 result;
  memcpy(
      result.fst, copy_of_re_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_ef_4f0(
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
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_As_plus_e_2d0(
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 = ZERO_ef_05();
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
          ntt_multiply_ef_b2(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_4f0(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_34(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static void generate_keypair_unpacked_a40(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_d6 *private_key,
    IndCpaPublicKeyUnpacked_d6 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_750(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[2U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_A, ret);
  sample_matrix_A_ee0(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b00(uu____2, copy_of_prf_input0, 0U);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[2U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_out_810(copy_of_prf_input, domain_separator)
          .fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compute_As_plus_e_2d0(public_key->t_as_ntt, public_key->A,
                        private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____5[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
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
static libcrux_ml_kem_utils_extraction_helper_Keypair512 generate_keypair_6a(
    Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_d6 private_key = default_1a_3c0();
  IndCpaPublicKeyUnpacked_d6 public_key = default_8d_890();
  generate_keypair_unpacked_a40(key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[800U];
  serialize_public_key_ca0(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key_990(private_key.secret_as_ntt, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[768U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[800U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair512 result;
  memcpy(result.fst, copy_of_secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  memcpy(result.snd, copy_of_public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_1f(
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
  H_a9_410(public_key, ret0);
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
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_ind_cca_generate_keypair_0b(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_6a(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key_1f(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1632U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_5e private_key =
      libcrux_ml_kem_types_from_7f_af(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_5e uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[800U];
  memcpy(copy_of_public_key, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_ee(
      uu____2, libcrux_ml_kem_types_from_5a_67(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_64(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_fb1(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_b21(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_fb1(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_74
sample_ring_element_cbd_a00(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_ef_05(););
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
  PRFxN_a9_b21(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_d7(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____1;);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[2U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 result;
  memcpy(
      result.fst, copy_of_error_1,
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
static KRML_MUSTINLINE void PRF_a9_162(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_960(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_8f0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_f7(&zeta_i, re);
  invert_ntt_at_layer_2_98(&zeta_i, re);
  invert_ntt_at_layer_3_fe(&zeta_i, re);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_bc(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_a9(re);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_vector_u_dd0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result0[i] = ZERO_ef_05(););
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
          ntt_multiply_ef_b2(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_4f0(&result0[i1], &product);
    }
    invert_ntt_montgomery_8f0(&result0[i1]);
    add_error_reduce_ef_dd(&result0[i1], &error_1[i1]);
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
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_ring_element_v_770(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_4f0(&result, &product););
  invert_ntt_montgomery_8f0(&result);
  result = add_message_error_reduce_ef_79(error_2, message, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- OUT_LEN= 640
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static void compress_then_serialize_u_420(
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
    compress_then_serialize_ring_element_u_9e0(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

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
static void encrypt_unpacked_a40(IndCpaPublicKeyUnpacked_d6 *public_key,
                                 uint8_t message[32U],
                                 Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_421(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____1 = sample_vector_cbd_then_ntt_out_810(copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____3 =
      sample_ring_element_cbd_a00(copy_of_prf_input, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_162(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_d7(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[2U];
  compute_vector_u_dd0(public_key->A, r_as_ntt, error_1, u);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_d3(copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_770(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[768U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[2U];
  memcpy(
      uu____5, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_420(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)640U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_d10(
      uu____6, Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                               (size_t)640U, uint8_t, size_t));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

/**
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
static void encrypt_6f(Eurydice_slice public_key, uint8_t message[32U],
                       Eurydice_slice randomness, uint8_t ret[768U]) {
  IndCpaPublicKeyUnpacked_d6 unpacked_public_key = default_8d_890();
  deserialize_ring_elements_reduced_530(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)768U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[2U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_422(seed, ret0);
  sample_matrix_A_ee0(uu____0, ret0, false);
  IndCpaPublicKeyUnpacked_d6 *uu____1 = &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t result[768U];
  encrypt_unpacked_a40(uu____1, copy_of_message, randomness, result);
  memcpy(ret, result, (size_t)768U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_16(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_a1(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_64(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  H_a9_410(Eurydice_array_to_slice(
               (size_t)800U, libcrux_ml_kem_types_as_slice_fd_fe0(public_key),
               uint8_t),
           ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_9f0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_fd_fe0(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_6f(uu____2, copy_of_randomness, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 ciphertext0 =
      libcrux_ml_kem_types_from_01_450(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  kdf_d8_16(shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 = ciphertext0;
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_secret_key_54(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_ef_05(););
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
        deserialize_to_uncompressed_ring_element_6c(secret_bytes);
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_250(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_05(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_790(u_bytes);
    ntt_vector_u_b70(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_message_7d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_ef_05();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_ef_b2(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_4f0(&result, &product););
  invert_ntt_montgomery_8f0(&result);
  result = subtract_reduce_ef_da(v, result);
  return result;
}

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
static void decrypt_unpacked_9d0(IndCpaPrivateKeyUnpacked_d6 *secret_key,
                                 uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  deserialize_then_decompress_u_250(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_b90(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_7d0(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_dd(message, ret0);
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
static void decrypt_75(Eurydice_slice secret_key, uint8_t *ciphertext,
                       uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  deserialize_secret_key_54(secret_key, secret_as_ntt);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_secret_as_ntt[2U];
  memcpy(
      copy_of_secret_as_ntt, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  IndCpaPrivateKeyUnpacked_d6 secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, copy_of_secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t result[32U];
  decrypt_unpacked_9d0(&secret_key_unpacked, ciphertext, result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void PRF_a9_161(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_96(input, ret);
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
void libcrux_ml_kem_ind_cca_decapsulate_7f(
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
  decrypt_75(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_9f0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_424(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_00_400(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_161(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
             implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_6f(uu____5, copy_of_decrypted, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_16(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  kdf_d8_16(shared_secret0, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_400(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}
