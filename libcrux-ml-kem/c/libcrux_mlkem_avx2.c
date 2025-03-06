/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a8f2211d1b95e0462a96382023b164a4116c7ca4
 * Eurydice: 788c5abefac3a9c7f79abae6a30fa8558e39764c
 * Karamel: 1d81d757d5d9e16dd6463ccc72324e587c707959
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: 1c4e2cbb4bc08f93cca04e22245f2b25dcb23d83
 */

#include "internal/libcrux_mlkem_avx2.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"
#include "internal/libcrux_sha3_avx2.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"
#include "libcrux_sha3.h"
#include "libcrux_sha3_avx2.h"

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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ZERO_9a(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array) {
  return mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_i16_array_9a(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_vec_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_vec_to_i16_array(
    __m256i v, int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, output, int16_t),
                         v);
  memcpy(ret, output, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_i16_array_9a(
    __m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_vec_to_i16_array(x, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_bytes(Eurydice_slice array) {
  return mm256_loadu_si256_u8(
      Eurydice_slice_subslice2(array, (size_t)0U, (size_t)32U, uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_bytes_9a(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_bytes(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_bytes(__m256i x,
                                                         Eurydice_slice bytes) {
  mm256_storeu_si256_u8(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)32U, uint8_t), x);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_bytes_9a(
    __m256i x, Eurydice_slice bytes) {
  libcrux_ml_kem_vector_avx2_to_bytes(x, bytes);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_add_9a(__m256i lhs,
                                                          __m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_sub_9a(__m256i lhs,
                                                          __m256i *rhs) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_multiply_by_constant_9a(__m256i vec, int16_t c) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_9a(
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

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_cond_subtract_3329(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_cond_subtract_3329_9a(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_cond_subtract_3329(vector);
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
  __m256i t512 = mm256_set1_epi16((int16_t)512);
  __m256i t1 = mm256_add_epi16(t0, t512);
  __m256i quotient = mm256_srai_epi16((int32_t)10, t1, __m256i);
  __m256i quotient_times_field_modulus = mm256_mullo_epi16(
      quotient, mm256_set1_epi16(LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return mm256_sub_epi16(vector, quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_barrett_reduce_9a(__m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_compress_1(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_1_9a(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_1(vector);
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_9a(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_layer_1_step(vector, zeta0, zeta1,
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_9a(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_layer_2_step(vector, zeta0, zeta1);
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

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_layer_3_step(__m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_layer_3_step_9a(__m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_layer_3_step(vector, zeta);
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_9a(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_9a(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step(vector, zeta0, zeta1);
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

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step(__m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_9a(
    __m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step(vector, zeta);
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

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_multiply(
    __m256i *lhs, __m256i *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_multiply_9a(
    __m256i *lhs, __m256i *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2,
                                                 zeta3);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    __m256i vector, uint8_t ret[2U]) {
  __m256i lsb_to_msb = mm256_slli_epi16((int32_t)15, vector, __m256i);
  __m128i low_msbs = mm256_castsi256_si128(lsb_to_msb);
  __m128i high_msbs = mm256_extracti128_si256((int32_t)1, lsb_to_msb, __m128i);
  __m128i msbs = mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = mm_movemask_epi8(msbs);
  uint8_t result[2U] = {(uint8_t)bits_packed, (uint8_t)(bits_packed >> 8U)};
  memcpy(ret, result, (size_t)2U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_1(__m256i vector,
                                                            uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_1_9a(
    __m256i vector, uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_1(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_i16s(
    int16_t a, int16_t b) {
  __m256i coefficients =
      mm256_set_epi16(b, b, b, b, b, b, b, b, a, a, a, a, a, a, a, a);
  __m256i coefficients_in_msb = mm256_mullo_epi16(
      coefficients,
      mm256_set_epi16((int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U,
                      (int16_t)1 << 11U, (int16_t)1 << 12U, (int16_t)1 << 13U,
                      (int16_t)1 << 14U, (int16_t)-32768, (int16_t)1 << 8U,
                      (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
                      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U,
                      (int16_t)-32768));
  return mm256_srli_epi16((int32_t)15, coefficients_in_msb, __m256i);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_u8s(
    uint8_t a, uint8_t b) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_i16s(
      (int16_t)a, (int16_t)b);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_u8s(
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_1(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_1_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_1(bytes);
}

/**
 `mm256_concat_pairs_n(n, x)` is then a sequence of 32 bits packets
 of the shape `0b0…0b₁…bₙa₁…aₙ`, if `x` is a sequence of pairs of
 16 bits, of the shape `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)` (where the last
 `n` bits are non-zero).
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(uint8_t n,
                                                          __m256i x) {
  int16_t n0 = (int16_t)1 << (uint32_t)n;
  return mm256_madd_epi16(
      x, mm256_set_epi16(n0, (int16_t)1, n0, (int16_t)1, n0, (int16_t)1, n0,
                         (int16_t)1, n0, (int16_t)1, n0, (int16_t)1, n0,
                         (int16_t)1, n0, (int16_t)1));
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    __m256i vector, uint8_t ret[8U]) {
  uint8_t serialized[16U] = {0U};
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(4U, vector);
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
  core_result_Result_15 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)8U, uint8_t),
      Eurydice_slice, uint8_t[8U]);
  core_result_unwrap_26_68(dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_4(__m256i vector,
                                                            uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_4_9a(
    __m256i vector, uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_4(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_i16s(
    int16_t b0, int16_t b1, int16_t b2, int16_t b3, int16_t b4, int16_t b5,
    int16_t b6, int16_t b7) {
  __m256i coefficients = mm256_set_epi16(b7, b7, b6, b6, b5, b5, b4, b4, b3, b3,
                                         b2, b2, b1, b1, b0, b0);
  __m256i coefficients_in_msb = mm256_mullo_epi16(
      coefficients,
      mm256_set_epi16((int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U));
  __m256i coefficients_in_lsb =
      mm256_srli_epi16((int32_t)4, coefficients_in_msb, __m256i);
  return mm256_and_si256(coefficients_in_lsb,
                         mm256_set1_epi16(((int16_t)1 << 4U) - (int16_t)1));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_u8s(
    uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3, uint8_t b4, uint8_t b5,
    uint8_t b6, uint8_t b7) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_i16s(
      (int16_t)b0, (int16_t)b1, (int16_t)b2, (int16_t)b3, (int16_t)b4,
      (int16_t)b5, (int16_t)b6, (int16_t)b7);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_u8s(
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
      Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_4(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_4_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_4(bytes);
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
  core_result_Result_9d dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t),
      Eurydice_slice, uint8_t[10U]);
  core_result_unwrap_26_ce(dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_5_9a(
    __m256i vector, uint8_t ret[10U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret);
}

/**
 We cannot model `mm256_inserti128_si256` on its own: it produces a
 Vec256 where the upper 128 bits are undefined. Thus
 `mm256_inserti128_si256` is not pure.

 Luckily, we always call `mm256_castsi128_si256` right after
 `mm256_inserti128_si256`: this composition sets the upper bits,
 making the whole computation pure again.
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(__m128i lower,
                                                                __m128i upper) {
  return mm256_inserti128_si256((int32_t)1, mm256_castsi128_si256(lower), upper,
                                __m256i);
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
  __m256i coefficients_loaded =
      libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
          coefficients, coefficients);
  __m256i coefficients0 = mm256_shuffle_epi8(
      coefficients_loaded,
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_5_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
    __m256i vector) {
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(10U, vector);
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
  __m128i upper_8 =
      mm256_extracti128_si256((int32_t)1, adjacent_8_combined, __m128i);
  return (
      CLITERAL(core_core_arch_x86___m128i_x2){.fst = lower_8, .snd = upper_8});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    __m256i vector, uint8_t ret[20U]) {
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
          vector);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  uint8_t serialized[32U] = {0U};
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice2(serialized, (size_t)10U,
                                                    (size_t)26U, uint8_t),
                        upper_8);
  uint8_t ret0[20U];
  core_result_Result_e1 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t),
      Eurydice_slice, uint8_t[20U]);
  core_result_unwrap_26_20(dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_10(__m256i vector,
                                                             uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_10_9a(
    __m256i vector, uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_10(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients = mm_shuffle_epi8(
      lower_coefficients0, mm_set_epi8(9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U, 4U, 3U,
                                       3U, 2U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = mm_shuffle_epi8(
      upper_coefficients0, mm_set_epi8(15U, 14U, 14U, 13U, 13U, 12U, 12U, 11U,
                                       10U, 9U, 9U, 8U, 8U, 7U, 7U, 6U));
  __m256i coefficients =
      libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
          lower_coefficients, upper_coefficients);
  __m256i coefficients0 = mm256_mullo_epi16(
      coefficients,
      mm256_set_epi16((int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
                      (int16_t)1 << 6U, (int16_t)1 << 0U, (int16_t)1 << 2U,
                      (int16_t)1 << 4U, (int16_t)1 << 6U, (int16_t)1 << 0U,
                      (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
                      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
                      (int16_t)1 << 6U));
  __m256i coefficients1 = mm256_srli_epi16((int32_t)6, coefficients0, __m256i);
  return mm256_and_si256(coefficients1,
                         mm256_set1_epi16(((int16_t)1 << 10U) - (int16_t)1));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes) {
  Eurydice_slice lower_coefficients =
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t);
  Eurydice_slice upper_coefficients =
      Eurydice_slice_subslice2(bytes, (size_t)4U, (size_t)20U, uint8_t);
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
      mm_loadu_si128(lower_coefficients), mm_loadu_si128(upper_coefficients));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_10(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_10_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_10(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    __m256i vector, uint8_t ret[22U]) {
  int16_t array[16U] = {0U};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, array, int16_t),
                         vector);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable_from_i16_array_2c(
          Eurydice_array_to_slice((size_t)16U, array, int16_t));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_11_2c(input, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_11_9a(
    __m256i vector, uint8_t ret[22U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_11_2c(bytes);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_2c(output, array);
  return mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_11_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_MUSTINLINE core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
    __m256i vector) {
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(12U, vector);
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
  return (
      CLITERAL(core_core_arch_x86___m128i_x2){.fst = lower_8, .snd = upper_8});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    __m256i vector, uint8_t ret[24U]) {
  uint8_t serialized[32U] = {0U};
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
          vector);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice2(serialized, (size_t)12U,
                                                    (size_t)28U, uint8_t),
                        upper_8);
  uint8_t ret0[24U];
  core_result_Result_b2 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)24U, uint8_t),
      Eurydice_slice, uint8_t[24U]);
  core_result_unwrap_26_70(dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_12(__m256i vector,
                                                             uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_12_9a(
    __m256i vector, uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_12(vector, ret);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients = mm_shuffle_epi8(
      lower_coefficients0, mm_set_epi8(11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U, 5U,
                                       4U, 4U, 3U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = mm_shuffle_epi8(
      upper_coefficients0, mm_set_epi8(15U, 14U, 14U, 13U, 12U, 11U, 11U, 10U,
                                       9U, 8U, 8U, 7U, 6U, 5U, 5U, 4U));
  __m256i coefficients =
      libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
          lower_coefficients, upper_coefficients);
  __m256i coefficients0 = mm256_mullo_epi16(
      coefficients,
      mm256_set_epi16((int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                      (int16_t)1 << 4U));
  __m256i coefficients1 = mm256_srli_epi16((int32_t)4, coefficients0, __m256i);
  return mm256_and_si256(coefficients1,
                         mm256_set1_epi16(((int16_t)1 << 12U) - (int16_t)1));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes) {
  __m128i lower_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  __m128i upper_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)8U, (size_t)24U, uint8_t));
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
      lower_coefficients, upper_coefficients);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_12(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_12_9a(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_12(bytes);
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_rej_sample_9a(
    Eurydice_slice input, Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#1}
*/
inline __m256i libcrux_ml_kem_vector_avx2_clone_3a(__m256i *self) {
  return self[0U];
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Repr for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_repr_11(__m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_vec_to_i16_array(x, ret);
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ZERO_ef_79(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 lit;
  __m256i repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_avx2_ZERO_9a(););
  memcpy(lit.coefficients, repeat_expression, (size_t)16U * sizeof(__m256i));
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_to_reduced_ring_element_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_9a(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_cond_subtract_3329_9a(coefficient);
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
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_ab(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *deserialized_pk) {
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
        deserialize_to_reduced_ring_element_79(ring_element);
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
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_ab(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_79(););
  deserialize_ring_elements_reduced_ab(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE __m256i shift_right_ef(__m256i vector) {
  return mm256_srai_epi16((int32_t)15, vector, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.shift_right_9a
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE __m256i shift_right_9a_ef(__m256i vector) {
  return shift_right_ef(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE __m256i to_unsigned_representative_79(__m256i a) {
  __m256i t = shift_right_9a_ef(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_9a(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_9a(a, &fm);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i to_unsigned_field_modulus_79(__m256i a) {
  return to_unsigned_representative_79(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = to_unsigned_field_modulus_79(re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2_serialize_12_9a(coefficient, bytes);
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void serialize_vector_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_79(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = t_as_ntt;
  serialize_vector_ab(
      uu____0,
      Eurydice_array_to_subslice2(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1184U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
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
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  serialize_public_key_mut_ed(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
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
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_ed(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[3U];
  deserialize_ring_elements_reduced_out_ab(
      Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_ed(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
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
static KRML_MUSTINLINE void H_a9_e0(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_ae(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U];
  H_a9_e0(Eurydice_array_to_subslice2(
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
bool libcrux_ml_kem_ind_cca_validate_private_key_12(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_ae(private_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_63_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 secret_as_ntt[3U];
} IndCpaPrivateKeyUnpacked_63;

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
static IndCpaPrivateKeyUnpacked_63 default_1a_ab(void) {
  IndCpaPrivateKeyUnpacked_63 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_ef_79(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct IndCpaPublicKeyUnpacked_63_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[3U][3U];
} IndCpaPublicKeyUnpacked_63;

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
static IndCpaPublicKeyUnpacked_63 default_8d_ab(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  uu____0[i] = ZERO_ef_79(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_63 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression0[3U][3U];
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[3U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      repeat_expression[i] = ZERO_ef_79(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)3U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6)););
  memcpy(lit.A, repeat_expression0,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6[3U]));
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
static KRML_MUSTINLINE void G_a9_e0(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_be(
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
  G_a9_e0(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_e0(uint8_t (*input)[34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
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
shake128_init_absorb_final_a9_e0(uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_e0(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_e0(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_e0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_first_three_blocks_e0(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_ed(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_e0(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_e0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_next_block_e0(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_ed0(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ZERO_79(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 lit;
  __m256i repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_avx2_ZERO_9a(););
  memcpy(lit.coefficients, repeat_expression, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
from_i16_array_79(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_79();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_from_i16_array_9a(Eurydice_slice_subslice2(
            a, i0 * (size_t)16U, (i0 + (size_t)1U) * (size_t)16U, int16_t));
  }
  return result;
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
from_i16_array_ef_79(Eurydice_slice a) {
  return from_i16_array_79(a);
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_f6 closure_6c1(
    int16_t s[272U]) {
  return from_i16_array_ef_79(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_6c1(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_e0(seeds);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_first_three_blocks_a9_e0(&xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_ed(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      shake128_squeeze_next_block_a9_e0(&xof_state, randomness);
      done = sample_from_uniform_distribution_next_ed0(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = closure_6c1(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_6c1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*A_transpose)[3U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[3U][34U]; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          core_array___core__clone__Clone_for__Array_T__N___20__clone(
              (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sampled[3U];
      sample_from_xof_6c1(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)3U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_41(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_41(uint8_t (*input)[33U],
                                        uint8_t ret[3U][128U]) {
  PRFxN_41(input, ret);
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
sample_from_binomial_distribution_2_79(Eurydice_slice randomness) {
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
  return from_i16_array_ef_79(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
sample_from_binomial_distribution_3_79(Eurydice_slice randomness) {
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
  return from_i16_array_ef_79(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
sample_from_binomial_distribution_89(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_79(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_9a(
        re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_avx2_sub_9a(re->coefficients[j], &t);
    re->coefficients[j] =
        libcrux_ml_kem_vector_avx2_add_9a(re->coefficients[j], &t);
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
static KRML_MUSTINLINE __m256i montgomery_multiply_fe_79(__m256i v,
                                                         int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
ntt_layer_int_vec_step_79(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i t = montgomery_multiply_fe_79(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_9a(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_9a(a, &t);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
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
          ntt_layer_int_vec_step_79(re->coefficients[j],
                                    re->coefficients[j + step_vec],
                                    libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
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
static KRML_MUSTINLINE void ntt_at_layer_3_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_9a(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_9a(
          re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_1_step_9a(
          re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)2U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)3U));
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    myself->coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_9a(myself->coefficients[i0]);
  }
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
static KRML_MUSTINLINE void poly_barrett_reduce_ef_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self) {
  poly_barrett_reduce_79(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  ntt_at_layer_7_79(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_79(&zeta_i, re);
  ntt_at_layer_2_79(&zeta_i, re);
  ntt_at_layer_1_79(&zeta_i, re);
  poly_barrett_reduce_ef_79(re);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b41(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  PRFxN_a9_41(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_89(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_79(&re_as_ntt[i0]););
  return domain_separator;
}

/**
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
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
ntt_multiply_79(libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
                libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 out = ZERO_79();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    out.coefficients[i0] = libcrux_ml_kem_vector_avx2_ntt_multiply_9a(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)1U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)2U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
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
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
ntt_multiply_ef_79(libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  return ntt_multiply_79(self, rhs);
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, myself->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    myself->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_9a(
        myself->coefficients[i0], &rhs->coefficients[i0]);
  }
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
static KRML_MUSTINLINE void add_to_ring_element_ef_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  add_to_ring_element_ab(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i to_standard_domain_79(__m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        to_standard_domain_79(myself->coefficients[j]);
    myself->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_9a(
        libcrux_ml_kem_vector_avx2_add_9a(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
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
static KRML_MUSTINLINE void add_standard_error_reduce_ef_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  add_standard_error_reduce_79(self, error);
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
static KRML_MUSTINLINE void compute_As_plus_e_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6[3U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6[3U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 = ZERO_ef_79();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_ab(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_79(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
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
static KRML_MUSTINLINE void generate_keypair_unpacked_221(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_63 *private_key,
    IndCpaPublicKeyUnpacked_63 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_be(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_6c1(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b41(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_as_ntt[i] = ZERO_ef_79(););
  LowStar_Ignore_ignore(
      sample_vector_cbd_then_ntt_b41(error_as_ntt, prf_input, domain_separator),
      uint8_t, void *);
  compute_As_plus_e_ab(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair768
serialize_unpacked_secret_key_ed(IndCpaPublicKeyUnpacked_63 *public_key,
                                 IndCpaPrivateKeyUnpacked_63 *private_key) {
  uint8_t public_key_serialized[1184U];
  serialize_public_key_ed(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U] = {0U};
  serialize_vector_ab(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)1152U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1152U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1184U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair768 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair768
generate_keypair_5d1(Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_63 private_key = default_1a_ab();
  IndCpaPublicKeyUnpacked_63 public_key = default_8d_ab();
  generate_keypair_unpacked_221(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_ed(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_ae(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t);
  uint8_t ret[32U];
  H_a9_e0(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_ae(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  serialize_kem_secret_key_mut_ae(private_key, public_key,
                                  implicit_rejection_value, out);
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
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_bb1(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_5d1(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key_ae(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 private_key =
      libcrux_ml_kem_types_from_9a_28(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_d9 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_74(
      uu____2, libcrux_ml_kem_types_from_5f_d0(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_be(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_fa1(
    Eurydice_slice public_key,
    IndCpaPublicKeyUnpacked_63 *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t);
  deserialize_ring_elements_reduced_ab(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[3U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_6c1(uu____1, ret, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_63
build_unpacked_public_key_fa1(Eurydice_slice public_key) {
  IndCpaPublicKeyUnpacked_63 unpacked_public_key = default_8d_ab();
  build_unpacked_public_key_mut_fa1(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[3size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_ed_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 fst[3U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 snd;
} tuple_ed;

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b41(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  PRFxN_a9_41(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          sample_from_binomial_distribution_89(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_a6(Eurydice_slice input, uint8_t ret[128U]) {
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
static KRML_MUSTINLINE void PRF_a9_410(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_9a(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)2U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)3U));
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_9a(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
                   zeta_i[0U] = zeta_i[0U] - (size_t)1U;
                   re->coefficients[round] =
                       libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_9a(
                           re->coefficients[round],
                           libcrux_ml_kem_polynomial_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
inv_ntt_layer_int_vec_step_reduce_79(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_9a(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_9a(
      libcrux_ml_kem_vector_avx2_add_9a(a, &b));
  b = montgomery_multiply_fe_79(a_minus_b, zeta_r);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_79(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
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
          inv_ntt_layer_int_vec_step_reduce_79(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
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
static KRML_MUSTINLINE void invert_ntt_montgomery_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_79(&zeta_i, re);
  invert_ntt_at_layer_2_79(&zeta_i, re);
  invert_ntt_at_layer_3_79(&zeta_i, re);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_79(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(
            myself->coefficients[j], (int16_t)1441);
    myself->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_9a(
        libcrux_ml_kem_vector_avx2_add_9a(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
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
static KRML_MUSTINLINE void add_error_reduce_ef_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  add_error_reduce_79(self, error);
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
static KRML_MUSTINLINE void compute_vector_u_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result[i] = ZERO_ef_79(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_f6[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_f6[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_ab(&result[i1], &product);
    }
    invert_ntt_montgomery_ab(&result[i1]);
    add_error_reduce_ef_79(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
compress_ciphertext_coefficient_ef(__m256i vector) {
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
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i compress_ef(__m256i vector) {
  return compress_ciphertext_coefficient_ef(vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_9a
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i compress_9a_ef(__m256i vector) {
  return compress_ef(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_0e0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_9a_ef(to_unsigned_field_modulus_79(re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2_serialize_10_9a(coefficient, bytes);
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
compress_ciphertext_coefficient_c4(__m256i vector) {
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
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i compress_c4(__m256i vector) {
  return compress_ciphertext_coefficient_c4(vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_9a
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i compress_9a_c4(__m256i vector) {
  return compress_c4(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_a4(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_0e0(re, uu____0);
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
static KRML_MUSTINLINE void compress_then_serialize_u_8c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_a4(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_ed
encrypt_c1_481(Eurydice_slice randomness,
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix)[3U],
               Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  r_as_ntt[i] = ZERO_ef_79(););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b41(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_ef_79(););
  uint8_t domain_separator =
      sample_ring_element_cbd_b41(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_410(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      sample_from_binomial_distribution_89(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u[3U];
  compute_vector_u_ab(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[3U];
  memcpy(
      uu____0, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  compress_then_serialize_u_8c(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 copy_of_r_as_ntt[3U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  tuple_ed lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  lit.snd = error_2;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i decompress_1_79(__m256i vec) {
  __m256i z = libcrux_ml_kem_vector_avx2_ZERO_9a();
  __m256i s = libcrux_ml_kem_vector_avx2_sub_9a(z, &vec);
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_9a(s,
                                                                 (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_message_79(uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_deserialize_1_9a(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t));
      re.coefficients[i0] = decompress_1_79(coefficient_compressed););
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
add_message_error_reduce_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(
            result.coefficients[i0], (int16_t)1441);
    __m256i tmp = libcrux_ml_kem_vector_avx2_add_9a(myself->coefficients[i0],
                                                    &message->coefficients[i0]);
    __m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_9a(coefficient_normal_form, &tmp);
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_9a(tmp0);
  }
  return result;
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
add_message_error_reduce_ef_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result) {
  return add_message_error_reduce_79(self, message, result);
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_ring_element_v_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_ab(&result, &product););
  invert_ntt_montgomery_ab(&result);
  return add_message_error_reduce_ef_79(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
compress_ciphertext_coefficient_d1(__m256i vector) {
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
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i compress_d1(__m256i vector) {
  return compress_ciphertext_coefficient_d1(vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_9a
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i compress_9a_d1(__m256i vector) {
  return compress_d1(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_9a_d1(to_unsigned_field_modulus_79(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_9a(coefficient, bytes);
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
compress_ciphertext_coefficient_f4(__m256i vector) {
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
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i compress_f4(__m256i vector) {
  return compress_ciphertext_coefficient_f4(vector);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_9a
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i compress_9a_f4(__m256i vector) {
  return compress_f4(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficients =
        compress_9a_f4(to_unsigned_representative_79(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_9a(coefficients, bytes);
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
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re, Eurydice_slice out) {
  compress_then_serialize_4_79(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message_as_ring_element =
      deserialize_then_decompress_message_79(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      compute_ring_element_v_ab(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_ed(v, ciphertext);
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
static KRML_MUSTINLINE void encrypt_unpacked_741(
    IndCpaPublicKeyUnpacked_63 *public_key, uint8_t *message,
    Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t ciphertext[1088U] = {0U};
  Eurydice_slice uu____0 = randomness;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[3U] =
      public_key->A;
  tuple_ed uu____2 =
      encrypt_c1_481(uu____0, uu____1,
                     Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                                 (size_t)960U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 = uu____2.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____3 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____4 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____5 = &error_2;
  uint8_t *uu____6 = message;
  encrypt_c2_ed(uu____3, uu____4, uu____5, uu____6,
                Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
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
static KRML_MUSTINLINE void encrypt_741(Eurydice_slice public_key,
                                        uint8_t *message,
                                        Eurydice_slice randomness,
                                        uint8_t ret[1088U]) {
  IndCpaPublicKeyUnpacked_63 unpacked_public_key =
      build_unpacked_public_key_fa1(public_key);
  uint8_t ret0[1088U];
  encrypt_unpacked_741(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)1088U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_ae(Eurydice_slice shared_secret,
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
tuple_c2 libcrux_ml_kem_ind_cca_encapsulate_701(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_be(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret0[32U];
  H_a9_e0(Eurydice_array_to_slice(
              (size_t)1184U, libcrux_ml_kem_types_as_slice_fd_d0(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_e0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1088U];
  encrypt_741(Eurydice_array_to_slice(
                  (size_t)1184U,
                  libcrux_ml_kem_types_as_slice_fd_d0(public_key), uint8_t),
              randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = libcrux_ml_kem_types_from_00_80(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_d8_ae(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_to_uncompressed_ring_element_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_12_9a(bytes);
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_vector_ab(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          deserialize_to_uncompressed_ring_element_79(Eurydice_slice_subslice2(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t));
      secret_as_ntt[i0] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_ef(__m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_9a with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_9a_ef(__m256i vector) {
  return decompress_ciphertext_coefficient_ef(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_10_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_9a(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_9a_ef(coefficient);
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
decompress_ciphertext_coefficient_c4(__m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_9a with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_9a_c4(__m256i vector) {
  return decompress_ciphertext_coefficient_c4(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_11_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_9a(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_9a_c4(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_ring_element_u_ee(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_79(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_ee(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_79(&zeta_i, re);
  ntt_at_layer_2_79(&zeta_i, re);
  ntt_at_layer_1_79(&zeta_i, re);
  poly_barrett_reduce_ef_79(re);
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
static KRML_MUSTINLINE void deserialize_then_decompress_u_ed(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_79(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_ee(u_bytes);
    ntt_vector_u_ee(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_d1(__m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_9a with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_9a_d1(__m256i vector) {
  return decompress_ciphertext_coefficient_d1(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_4_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_9a(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_9a_d1(coefficient);
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
decompress_ciphertext_coefficient_f4(__m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#3}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_9a with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_9a_f4(__m256i vector) {
  return decompress_ciphertext_coefficient_f4(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_5_79(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = ZERO_ef_79();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_9a(bytes);
    re.coefficients[i0] =
        decompress_ciphertext_coefficient_9a_f4(re.coefficients[i0]);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_ring_element_v_ed(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_79(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
subtract_reduce_79(libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_9a(
            b.coefficients[i0], (int16_t)1441);
    b.coefficients[i0] = libcrux_ml_kem_vector_avx2_barrett_reduce_9a(
        libcrux_ml_kem_vector_avx2_sub_9a(myself->coefficients[i0],
                                          &coefficient_normal_form));
  }
  return b;
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
subtract_reduce_ef_79(libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 b) {
  return subtract_reduce_79(self, b);
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_message_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_ab(&result, &product););
  invert_ntt_montgomery_ab(&result);
  return subtract_reduce_ef_79(v, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_79(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient = to_unsigned_field_modulus_79(re.coefficients[i0]);
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_9a(coefficient);
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_avx2_serialize_1_9a(coefficient_compressed, bytes);
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
static KRML_MUSTINLINE void decrypt_unpacked_2f(
    IndCpaPrivateKeyUnpacked_63 *secret_key, uint8_t *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[3U];
  deserialize_then_decompress_u_ed(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      deserialize_then_decompress_ring_element_v_ed(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message =
      compute_message_ab(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_79(message, ret0);
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
static KRML_MUSTINLINE void decrypt_2f(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  IndCpaPrivateKeyUnpacked_63 secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = ZERO_ef_79(););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  deserialize_vector_ab(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_2f(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_9e(Eurydice_slice input, uint8_t ret[32U]) {
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
static KRML_MUSTINLINE void PRF_a9_41(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
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
void libcrux_ml_kem_ind_cca_decapsulate_a11(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_2f(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_e0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_43_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_41(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[1088U];
  encrypt_741(ind_cpa_public_key, decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_ae(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_ae(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_43_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_42(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *deserialized_pk) {
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
        deserialize_to_reduced_ring_element_79(ring_element);
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
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_42(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_79(););
  deserialize_ring_elements_reduced_42(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void serialize_vector_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_79(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_78(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = t_as_ntt;
  serialize_vector_42(
      uu____0,
      Eurydice_array_to_subslice2(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1568U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
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
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_78(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  serialize_public_key_mut_78(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
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
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_78(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[4U];
  deserialize_ring_elements_reduced_out_42(
      Eurydice_array_to_subslice_to(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_78(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
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
static KRML_MUSTINLINE void H_a9_ac(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_5e(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  uint8_t t[32U];
  H_a9_ac(Eurydice_array_to_subslice2(
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
bool libcrux_ml_kem_ind_cca_validate_private_key_b9(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_64 *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_5e(private_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_39_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 secret_as_ntt[4U];
} IndCpaPrivateKeyUnpacked_39;

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
static IndCpaPrivateKeyUnpacked_39 default_1a_42(void) {
  IndCpaPrivateKeyUnpacked_39 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_ef_79(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct IndCpaPublicKeyUnpacked_39_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[4U][4U];
} IndCpaPublicKeyUnpacked_39;

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
static IndCpaPublicKeyUnpacked_39 default_8d_42(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  uu____0[i] = ZERO_ef_79(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_39 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression0[4U][4U];
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[4U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      repeat_expression[i] = ZERO_ef_79(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)4U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6)););
  memcpy(lit.A, repeat_expression0,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6[4U]));
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
static KRML_MUSTINLINE void G_a9_ac(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_6a(
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
  G_a9_ac(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_ac(uint8_t (*input)[34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
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
shake128_init_absorb_final_a9_ac(uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_ac(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_ac(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_ac(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_first_three_blocks_ac(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_78(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_ac(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_ac(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_next_block_ac(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_780(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_f6 closure_6c(
    int16_t s[272U]) {
  return from_i16_array_ef_79(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_6c(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_ac(seeds);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_first_three_blocks_a9_ac(&xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_78(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      shake128_squeeze_next_block_a9_ac(&xof_state, randomness);
      done = sample_from_uniform_distribution_next_780(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[4U][272U];
  memcpy(copy_of_out, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = closure_6c(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*A_transpose)[4U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[4U][34U]; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          core_array___core__clone__Clone_for__Array_T__N___20__clone(
              (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sampled[4U];
      sample_from_xof_6c(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)4U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_44(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_44(uint8_t (*input)[33U],
                                        uint8_t ret[4U][128U]) {
  PRFxN_44(input, ret);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b4(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[4U][128U];
  PRFxN_a9_44(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_89(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_79(&re_as_ntt[i0]););
  return domain_separator;
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, myself->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    myself->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_9a(
        myself->coefficients[i0], &rhs->coefficients[i0]);
  }
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
static KRML_MUSTINLINE void add_to_ring_element_ef_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  add_to_ring_element_42(self, rhs);
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
static KRML_MUSTINLINE void compute_As_plus_e_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6[4U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6[4U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 = ZERO_ef_79();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)4U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_42(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_79(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
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
static KRML_MUSTINLINE void generate_keypair_unpacked_22(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_39 *private_key,
    IndCpaPublicKeyUnpacked_39 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_6a(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[4U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_6c(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b4(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_as_ntt[i] = ZERO_ef_79(););
  LowStar_Ignore_ignore(
      sample_vector_cbd_then_ntt_b4(error_as_ntt, prf_input, domain_separator),
      uint8_t, void *);
  compute_As_plus_e_42(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair1024
serialize_unpacked_secret_key_1e(IndCpaPublicKeyUnpacked_39 *public_key,
                                 IndCpaPrivateKeyUnpacked_39 *private_key) {
  uint8_t public_key_serialized[1568U];
  serialize_public_key_78(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U] = {0U};
  serialize_vector_42(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)1536U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1536U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1568U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair1024
generate_keypair_5d0(Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_39 private_key = default_1a_42();
  IndCpaPublicKeyUnpacked_39 public_key = default_8d_42();
  generate_keypair_unpacked_22(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_1e(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_5e(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t);
  uint8_t ret[32U];
  H_a9_ac(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_5e(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[3168U]) {
  uint8_t out[3168U] = {0U};
  serialize_kem_secret_key_mut_5e(private_key, public_key,
                                  implicit_rejection_value, out);
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
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_bb0(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_5d0(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key_5e(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[3168U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_83 private_key =
      libcrux_ml_kem_types_from_9a_39(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_83 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1568U];
  memcpy(copy_of_public_key, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_94(
      uu____2, libcrux_ml_kem_types_from_5f_af(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_6a(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_fa0(
    Eurydice_slice public_key,
    IndCpaPublicKeyUnpacked_39 *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t);
  deserialize_ring_elements_reduced_42(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1536U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[4U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_6c(uu____1, ret, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_39
build_unpacked_public_key_fa0(Eurydice_slice public_key) {
  IndCpaPublicKeyUnpacked_39 unpacked_public_key = default_8d_42();
  build_unpacked_public_key_mut_fa0(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[4size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_08_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 fst[4U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 snd;
} tuple_08;

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b4(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[4U][128U];
  PRFxN_a9_44(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          sample_from_binomial_distribution_89(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
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
static KRML_MUSTINLINE void PRF_a9_440(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_79(&zeta_i, re);
  invert_ntt_at_layer_2_79(&zeta_i, re);
  invert_ntt_at_layer_3_79(&zeta_i, re);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_79(re);
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
static KRML_MUSTINLINE void compute_vector_u_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result[i] = ZERO_ef_79(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)4U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_f6[4U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_f6[4U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_42(&result[i1], &product);
    }
    invert_ntt_montgomery_42(&result[i1]);
    add_error_reduce_ef_79(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_0e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_9a_c4(to_unsigned_representative_79(re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2_serialize_11_9a(coefficient, bytes);
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
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_6f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_0e(re, uu____0);
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
static KRML_MUSTINLINE void compress_then_serialize_u_c9(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 input[4U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t);
    uint8_t ret[352U];
    compress_then_serialize_ring_element_u_6f(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)352U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_08
encrypt_c1_48(Eurydice_slice randomness,
              libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix)[4U],
              Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  r_as_ntt[i] = ZERO_ef_79(););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b4(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_ef_79(););
  uint8_t domain_separator =
      sample_ring_element_cbd_b4(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_440(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      sample_from_binomial_distribution_89(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u[4U];
  compute_vector_u_42(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[4U];
  memcpy(
      uu____0, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  compress_then_serialize_u_c9(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 copy_of_r_as_ntt[4U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  tuple_08 lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  lit.snd = error_2;
  return lit;
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_ring_element_v_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_42(&result, &product););
  invert_ntt_montgomery_42(&result);
  return add_message_error_reduce_ef_79(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_1e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re, Eurydice_slice out) {
  compress_then_serialize_5_79(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_1e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message_as_ring_element =
      deserialize_then_decompress_message_79(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      compute_ring_element_v_42(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_1e(v, ciphertext);
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
static KRML_MUSTINLINE void encrypt_unpacked_74(
    IndCpaPublicKeyUnpacked_39 *public_key, uint8_t *message,
    Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t ciphertext[1568U] = {0U};
  Eurydice_slice uu____0 = randomness;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[4U] =
      public_key->A;
  tuple_08 uu____2 =
      encrypt_c1_48(uu____0, uu____1,
                    Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                                (size_t)1408U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____2.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 = uu____2.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____3 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____4 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____5 = &error_2;
  uint8_t *uu____6 = message;
  encrypt_c2_1e(uu____3, uu____4, uu____5, uu____6,
                Eurydice_array_to_subslice_from(
                    (size_t)1568U, ciphertext, (size_t)1408U, uint8_t, size_t));
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
static KRML_MUSTINLINE void encrypt_740(Eurydice_slice public_key,
                                        uint8_t *message,
                                        Eurydice_slice randomness,
                                        uint8_t ret[1568U]) {
  IndCpaPublicKeyUnpacked_39 unpacked_public_key =
      build_unpacked_public_key_fa0(public_key);
  uint8_t ret0[1568U];
  encrypt_unpacked_74(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)1568U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_5e(Eurydice_slice shared_secret,
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
tuple_fa libcrux_ml_kem_ind_cca_encapsulate_700(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_6a(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret0[32U];
  H_a9_ac(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_fd_af(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_ac(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1568U];
  encrypt_740(Eurydice_array_to_slice(
                  (size_t)1568U,
                  libcrux_ml_kem_types_as_slice_fd_af(public_key), uint8_t),
              randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  tuple_fa lit;
  lit.fst = libcrux_ml_kem_types_from_00_af(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_d8_5e(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_vector_42(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          deserialize_to_uncompressed_ring_element_79(Eurydice_slice_subslice2(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t));
      secret_as_ntt[i0] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_ring_element_u_85(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_79(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_85(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_79(&zeta_i, re);
  ntt_at_layer_2_79(&zeta_i, re);
  ntt_at_layer_1_79(&zeta_i, re);
  poly_barrett_reduce_ef_79(re);
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
static KRML_MUSTINLINE void deserialize_then_decompress_u_1e(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_79(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_85(u_bytes);
    ntt_vector_u_85(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_ring_element_v_78(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_79(serialized);
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_message_42(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_42(&result, &product););
  invert_ntt_montgomery_42(&result);
  return subtract_reduce_ef_79(v, result);
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
static KRML_MUSTINLINE void decrypt_unpacked_37(
    IndCpaPrivateKeyUnpacked_39 *secret_key, uint8_t *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[4U];
  deserialize_then_decompress_u_1e(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      deserialize_then_decompress_ring_element_v_78(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message =
      compute_message_42(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_79(message, ret0);
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
static KRML_MUSTINLINE void decrypt_37(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  IndCpaPrivateKeyUnpacked_39 secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = ZERO_ef_79(););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  deserialize_vector_42(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_37(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void PRF_a9_44(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
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
void libcrux_ml_kem_ind_cca_decapsulate_a10(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_37(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_ac(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_7f(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_43_af(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_44(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[1568U];
  encrypt_740(ind_cpa_public_key, decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_5e(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_5e(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_43_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_89(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *deserialized_pk) {
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
        deserialize_to_reduced_ring_element_79(ring_element);
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
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_89(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_ef_79(););
  deserialize_ring_elements_reduced_89(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void serialize_vector_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_79(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_mut_29(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = t_as_ntt;
  serialize_vector_89(
      uu____0,
      Eurydice_array_to_subslice2(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)800U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
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
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_29(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  serialize_public_key_mut_29(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)800U * sizeof(uint8_t));
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
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_29(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[2U];
  deserialize_ring_elements_reduced_out_89(
      Eurydice_array_to_subslice_to(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key_29(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
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
static KRML_MUSTINLINE void H_a9_fd(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_4d(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key) {
  uint8_t t[32U];
  H_a9_fd(Eurydice_array_to_subslice2(
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
bool libcrux_ml_kem_ind_cca_validate_private_key_ad(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_4d(private_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct IndCpaPrivateKeyUnpacked_94_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 secret_as_ntt[2U];
} IndCpaPrivateKeyUnpacked_94;

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
static IndCpaPrivateKeyUnpacked_94 default_1a_89(void) {
  IndCpaPrivateKeyUnpacked_94 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] = ZERO_ef_79(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct IndCpaPublicKeyUnpacked_94_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[2U][2U];
} IndCpaPublicKeyUnpacked_94;

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
static IndCpaPublicKeyUnpacked_94 default_8d_89(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  uu____0[i] = ZERO_ef_79(););
  uint8_t uu____1[32U] = {0U};
  IndCpaPublicKeyUnpacked_94 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression0[2U][2U];
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 repeat_expression[2U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      repeat_expression[i] = ZERO_ef_79(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)2U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6)););
  memcpy(lit.A, repeat_expression0,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6[2U]));
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
static KRML_MUSTINLINE void G_a9_fd(Eurydice_slice input, uint8_t ret[64U]) {
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
static KRML_MUSTINLINE void cpa_keygen_seed_d8_f8(
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
  G_a9_fd(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_fd(uint8_t (*input)[34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
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
shake128_init_absorb_final_a9_fd(uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_fd(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_fd(
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_fd(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_first_three_blocks_fd(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_29(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_fd(
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_fd(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_next_block_fd(self, ret);
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
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_290(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
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
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_9a(
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_f6 closure_6c0(
    int16_t s[272U]) {
  return from_i16_array_ef_79(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_from_xof_6c0(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_fd(seeds);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_first_three_blocks_a9_fd(&xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_29(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      shake128_squeeze_next_block_a9_fd(&xof_state, randomness);
      done = sample_from_uniform_distribution_next_290(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[2U][272U];
  memcpy(copy_of_out, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = closure_6c0(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_6c0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*A_transpose)[2U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[2U][34U]; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          core_array___core__clone__Clone_for__Array_T__N___20__clone(
              (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sampled[2U];
      sample_from_xof_6c0(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)2U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_f6 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_49(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_49(uint8_t (*input)[33U],
                                        uint8_t ret[2U][192U]) {
  PRFxN_49(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
sample_from_binomial_distribution_ab(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_79(randomness);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b40(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(prf_inputs, domain_separator);
  uint8_t prf_outputs[2U][192U];
  PRFxN_a9_49(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_ab(
          Eurydice_array_to_slice((size_t)192U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_79(&re_as_ntt[i0]););
  return domain_separator;
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, myself->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    myself->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_9a(
        myself->coefficients[i0], &rhs->coefficients[i0]);
  }
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
static KRML_MUSTINLINE void add_to_ring_element_ef_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  add_to_ring_element_89(self, rhs);
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
static KRML_MUSTINLINE void compute_As_plus_e_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6[2U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6[2U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 = ZERO_ef_79();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)2U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_ef_89(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_ef_79(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
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
static KRML_MUSTINLINE void generate_keypair_unpacked_220(
    Eurydice_slice key_generation_seed,
    IndCpaPrivateKeyUnpacked_94 *private_key,
    IndCpaPublicKeyUnpacked_94 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_d8_f8(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[2U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_6c0(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b40(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_as_ntt[i] = ZERO_ef_79(););
  LowStar_Ignore_ignore(
      sample_vector_cbd_then_ntt_b40(error_as_ntt, prf_input, domain_separator),
      uint8_t, void *);
  compute_As_plus_e_89(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair512
serialize_unpacked_secret_key_ba(IndCpaPublicKeyUnpacked_94 *public_key,
                                 IndCpaPrivateKeyUnpacked_94 *private_key) {
  uint8_t public_key_serialized[800U];
  serialize_public_key_29(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[768U] = {0U};
  serialize_vector_89(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)768U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[768U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[800U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair512 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair512
generate_keypair_5d(Eurydice_slice key_generation_seed) {
  IndCpaPrivateKeyUnpacked_94 private_key = default_1a_89();
  IndCpaPublicKeyUnpacked_94 public_key = default_8d_89();
  generate_keypair_unpacked_220(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_ba(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_4d(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t);
  uint8_t ret[32U];
  H_a9_fd(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_4d(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[1632U]) {
  uint8_t out[1632U] = {0U};
  serialize_kem_secret_key_mut_4d(private_key, public_key,
                                  implicit_rejection_value, out);
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
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_3e libcrux_ml_kem_ind_cca_generate_keypair_bb(
    uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_5d(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key_4d(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1632U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_fa private_key =
      libcrux_ml_kem_types_from_9a_2a(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_fa uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[800U];
  memcpy(copy_of_public_key, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_3a_fa(
      uu____2, libcrux_ml_kem_types_from_5f_4d(copy_of_public_key));
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
static KRML_MUSTINLINE void entropy_preprocess_d8_f8(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_fa(
    Eurydice_slice public_key,
    IndCpaPublicKeyUnpacked_94 *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t);
  deserialize_ring_elements_reduced_89(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)768U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[2U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_6c0(uu____1, ret, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_94
build_unpacked_public_key_fa(Eurydice_slice public_key) {
  IndCpaPublicKeyUnpacked_94 unpacked_public_key = default_8d_89();
  build_unpacked_public_key_mut_fa(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[2size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_35_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 fst[2U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 snd;
} tuple_35;

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_490(uint8_t (*input)[33U],
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
static KRML_MUSTINLINE void PRFxN_a9_490(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_490(input, ret);
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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b40(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1) {
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  core_array___core__clone__Clone_for__Array_T__N___20__clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(prf_inputs, domain_separator);
  uint8_t prf_outputs[2U][128U];
  PRFxN_a9_490(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          sample_from_binomial_distribution_89(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
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
static KRML_MUSTINLINE void PRF_a9_490(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_79(&zeta_i, re);
  invert_ntt_at_layer_2_79(&zeta_i, re);
  invert_ntt_at_layer_3_79(&zeta_i, re);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_79(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_ef_79(re);
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
static KRML_MUSTINLINE void compute_vector_u_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result[i] = ZERO_ef_79(););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)2U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_f6[2U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_f6[2U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
          ntt_multiply_ef_79(a_element, &r_as_ntt[j]);
      add_to_ring_element_ef_89(&result[i1], &product);
    }
    invert_ntt_montgomery_89(&result[i1]);
    add_error_reduce_ef_79(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
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
static KRML_MUSTINLINE void compress_then_serialize_u_2d(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 input[2U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_a4(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_35
encrypt_c1_480(Eurydice_slice randomness,
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6 (*matrix)[2U],
               Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  r_as_ntt[i] = ZERO_ef_79(););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b40(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_ef_79(););
  uint8_t domain_separator =
      sample_ring_element_cbd_b40(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_490(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      sample_from_binomial_distribution_89(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u[2U];
  compute_vector_u_89(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[2U];
  memcpy(
      uu____0, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  compress_then_serialize_u_2d(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 copy_of_r_as_ntt[2U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  tuple_35 lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  lit.snd = error_2;
  return lit;
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_ring_element_v_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_ef_89(&result, &product););
  invert_ntt_montgomery_89(&result);
  return add_message_error_reduce_ef_79(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_ba(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re, Eurydice_slice out) {
  compress_then_serialize_4_79(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_ba(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message_as_ring_element =
      deserialize_then_decompress_message_79(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      compute_ring_element_v_89(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_ba(v, ciphertext);
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
static KRML_MUSTINLINE void encrypt_unpacked_740(
    IndCpaPublicKeyUnpacked_94 *public_key, uint8_t *message,
    Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t ciphertext[768U] = {0U};
  Eurydice_slice uu____0 = randomness;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6(*uu____1)[2U] =
      public_key->A;
  tuple_35 uu____2 =
      encrypt_c1_480(uu____0, uu____1,
                     Eurydice_array_to_subslice2(ciphertext, (size_t)0U,
                                                 (size_t)640U, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____2.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 = uu____2.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____3 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____4 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____5 = &error_2;
  uint8_t *uu____6 = message;
  encrypt_c2_ba(uu____3, uu____4, uu____5, uu____6,
                Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
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
static KRML_MUSTINLINE void encrypt_74(Eurydice_slice public_key,
                                       uint8_t *message,
                                       Eurydice_slice randomness,
                                       uint8_t ret[768U]) {
  IndCpaPublicKeyUnpacked_94 unpacked_public_key =
      build_unpacked_public_key_fa(public_key);
  uint8_t ret0[768U];
  encrypt_unpacked_740(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)768U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void kdf_d8_4d(Eurydice_slice shared_secret,
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
tuple_41 libcrux_ml_kem_ind_cca_encapsulate_70(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_d8_f8(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret0[32U];
  H_a9_fd(Eurydice_array_to_slice(
              (size_t)800U, libcrux_ml_kem_types_as_slice_fd_4d(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_a9_fd(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[768U];
  encrypt_74(Eurydice_array_to_slice(
                 (size_t)800U, libcrux_ml_kem_types_as_slice_fd_4d(public_key),
                 uint8_t),
             randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  tuple_41 lit;
  lit.fst = libcrux_ml_kem_types_from_00_d0(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_d8_4d(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_vector_89(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt) {
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          deserialize_to_uncompressed_ring_element_79(Eurydice_slice_subslice2(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t));
      secret_as_ntt[i0] = uu____0;);
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
static KRML_MUSTINLINE void deserialize_then_decompress_u_ba(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  u_as_ntt[i] = ZERO_ef_79(););
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
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_ee(u_bytes);
    ntt_vector_u_ee(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
deserialize_then_decompress_ring_element_v_29(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_79(serialized);
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_f6
compute_message_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 result = ZERO_ef_79();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 product =
                      ntt_multiply_ef_79(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_ef_89(&result, &product););
  invert_ntt_montgomery_89(&result);
  return subtract_reduce_ef_79(v, result);
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
static KRML_MUSTINLINE void decrypt_unpacked_4b(
    IndCpaPrivateKeyUnpacked_94 *secret_key, uint8_t *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[2U];
  deserialize_then_decompress_u_ba(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      deserialize_then_decompress_ring_element_v_29(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message =
      compute_message_89(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_79(message, ret0);
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
static KRML_MUSTINLINE void decrypt_4b(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  IndCpaPrivateKeyUnpacked_94 secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = ZERO_ef_79(););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  deserialize_vector_89(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_4b(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void PRF_a9_49(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
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
void libcrux_ml_kem_ind_cca_decapsulate_a1(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_4b(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_a9_fd(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_4d(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_43_d0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_49(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[768U];
  encrypt_74(ind_cpa_public_key, decrypted, pseudorandomness,
             expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_d8_4d(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_d8_4d(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_43_d0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}
