/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 65c45918a38d1b3e2155d3d69e9831b670d0a09f
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: baec61db14d5132ae8eb4bd7a288638b7f2f1db8
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 6a8770c9d9d51b553169e0f2cc8cfd808fc7caa6
 */

#ifndef __libcrux_mlkem768_avx2_H
#define __libcrux_mlkem768_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_core.h"
#include "libcrux_ct_ops.h"
#include "libcrux_mlkem768_avx2_types.h"
#include "libcrux_mlkem768_portable.h"
#include "libcrux_mlkem768_portable_types.h"
#include "libcrux_sha3_avx2.h"
#include "libcrux_sha3_portable.h"

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G(
    Eurydice_slice input, uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H(
    Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_zero(void) {
  return libcrux_intrinsics_avx2_mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_ZERO_ea(void) {
  return libcrux_ml_kem_vector_avx2_zero();
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array) {
  return libcrux_intrinsics_avx2_mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_from_i16_array_ea(
    Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_i16_array(array);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_i16_array(
    __m256i v, int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, output, int16_t), v);
  memcpy(ret, output, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_to_i16_array_ea(
    __m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_to_i16_array(x, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_to_bytes_ea(__m256i x,
                                                          Eurydice_slice out) {
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(out, x);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_from_bytes_ea(
    Eurydice_slice bytes) {
  return libcrux_intrinsics_avx2_mm256_loadu_si256_u8(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs, __m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_add_ea(__m256i lhs,
                                                        __m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs, __m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_sub_ea(__m256i lhs,
                                                        __m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(__m256i vector,
                                                           int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_mullo_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
    __m256i v, int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(v, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_and_si256(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
    __m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vector, constant);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(__m256i vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i v_minus_field_modulus =
      libcrux_intrinsics_avx2_mm256_sub_epi16(vector, field_modulus);
  __m256i sign_mask = libcrux_intrinsics_avx2_mm256_srai_epi16(
      (int32_t)15, v_minus_field_modulus, __m256i);
  __m256i conditional_add_field_modulus =
      libcrux_intrinsics_avx2_mm256_and_si256(sign_mask, field_modulus);
  return libcrux_intrinsics_avx2_mm256_add_epi16(v_minus_field_modulus,
                                                 conditional_add_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i vector) {
  __m256i t = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(
                  LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  __m256i t0 = libcrux_intrinsics_avx2_mm256_add_epi16(
      t, libcrux_intrinsics_avx2_mm256_set1_epi16((int16_t)512));
  __m256i quotient =
      libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)10, t0, __m256i);
  __m256i quotient_times_field_modulus =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(
          quotient, libcrux_intrinsics_avx2_mm256_set1_epi16(
                        LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return libcrux_intrinsics_avx2_mm256_sub_epi16(vector,
                                                 quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i vector, int16_t constant) {
  __m256i constant0 = libcrux_intrinsics_avx2_mm256_set1_epi16(constant);
  __m256i value_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(vector, constant0);
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      k, libcrux_intrinsics_avx2_mm256_set1_epi16(
             LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(vector, constant0);
  return libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
    __m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    __m256i vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)2);
  __m256i field_modulus_quartered = libcrux_intrinsics_avx2_mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)4);
  __m256i shifted =
      libcrux_intrinsics_avx2_mm256_sub_epi16(field_modulus_halved, vector);
  __m256i mask =
      libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, shifted, __m256i);
  __m256i shifted_to_positive =
      libcrux_intrinsics_avx2_mm256_xor_si256(mask, shifted);
  __m256i shifted_to_positive_in_range =
      libcrux_intrinsics_avx2_mm256_sub_epi16(shifted_to_positive,
                                              field_modulus_quartered);
  return libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)15, shifted_to_positive_in_range, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_compress_1_ea(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(__m256i lhs,
                                                      __m256i rhs) {
  __m256i prod02 = libcrux_intrinsics_avx2_mm256_mul_epu32(lhs, rhs);
  __m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epu32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, lhs, __m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, rhs, __m256i));
  return libcrux_intrinsics_avx2_mm256_unpackhi_epi64(
      libcrux_intrinsics_avx2_mm256_unpacklo_epi32(prod02, prod13),
      libcrux_intrinsics_avx2_mm256_unpackhi_epi32(prod02, prod13));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    __m256i v, __m256i c) {
  __m256i value_low = libcrux_intrinsics_avx2_mm256_mullo_epi16(v, c);
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      k, libcrux_intrinsics_avx2_mm256_set1_epi16(
             LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high = libcrux_intrinsics_avx2_mm256_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1,
      -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245,
                                                            vector, __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)160,
                                                            vector, __m256i);
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0,
      -zeta0, -zeta0, -zeta0, zeta0, zeta0, zeta0, zeta0);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)238,
                                                            vector, __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs =
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)68, vector, __m256i);
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    __m128i v, __m128i c) {
  __m128i value_low = libcrux_intrinsics_avx2_mm_mullo_epi16(v, c);
  __m128i k = libcrux_intrinsics_avx2_mm_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m128i k_times_modulus = libcrux_intrinsics_avx2_mm_mulhi_epi16(
      k, libcrux_intrinsics_avx2_mm_set1_epi16(
             LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m128i value_high = libcrux_intrinsics_avx2_mm_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_mm_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(__m256i vector, int16_t zeta) {
  __m128i rhs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m128i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          rhs, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  __m128i lhs = libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs0);
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs0);
  __m256i combined =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  return libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(
    __m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(__m256i vector,
                                                    int16_t zeta0,
                                                    int16_t zeta1,
                                                    int16_t zeta2,
                                                    int16_t zeta3) {
  __m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245,
                                                            vector, __m256i);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)160,
                                                            vector, __m256i);
  __m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1,
               (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1));
  __m256i sum0 = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum0, libcrux_intrinsics_avx2_mm256_set_epi16(
                    zeta3, zeta3, (int16_t)0, (int16_t)0, zeta2, zeta2,
                    (int16_t)0, (int16_t)0, zeta1, zeta1, (int16_t)0,
                    (int16_t)0, zeta0, zeta0, (int16_t)0, (int16_t)0));
  __m256i sum = libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(sum0);
  return libcrux_intrinsics_avx2_mm256_blend_epi16((int32_t)204, sum,
                                                   sum_times_zetas, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(__m256i vector,
                                                    int16_t zeta0,
                                                    int16_t zeta1) {
  __m256i lhs = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)245, vector, __m256i);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)160, vector, __m256i);
  __m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)1,
               (int16_t)1));
  __m256i sum = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum, libcrux_intrinsics_avx2_mm256_set_epi16(
                   zeta1, zeta1, zeta1, zeta1, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, zeta0, zeta0, zeta0, zeta0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0));
  return libcrux_intrinsics_avx2_mm256_blend_epi16((int32_t)240, sum,
                                                   sum_times_zetas, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(
    __m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(__m256i vector,
                                                    int16_t zeta) {
  __m128i lhs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m128i rhs = libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs);
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs);
  __m128i upper_coefficients0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          upper_coefficients, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  __m256i combined =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  return libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients0, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(
    __m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(__m256i v) {
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      v,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      k, libcrux_intrinsics_avx2_mm256_set1_epi32(
             (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)16, v, __m256i);
  __m256i result =
      libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
  __m256i result0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)16, result, __m256i);
  return libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)16, result0,
                                                  __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(
    __m256i lhs, __m256i rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i shuffle_with = libcrux_intrinsics_avx2_mm256_set_epi8(
      (int8_t)15, (int8_t)14, (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6,
      (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8,
      (int8_t)5, (int8_t)4, (int8_t)1, (int8_t)0, (int8_t)15, (int8_t)14,
      (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6, (int8_t)3, (int8_t)2,
      (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
      (int8_t)1, (int8_t)0);
  __m256i lhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(lhs, shuffle_with);
  __m256i lhs_shuffled0 = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, lhs_shuffled, __m256i);
  __m128i lhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(lhs_shuffled0);
  __m256i lhs_evens0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_evens);
  __m128i lhs_odds = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, lhs_shuffled0, __m128i);
  __m256i lhs_odds0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_odds);
  __m256i rhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(rhs, shuffle_with);
  __m256i rhs_shuffled0 = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, rhs_shuffled, __m256i);
  __m128i rhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(rhs_shuffled0);
  __m256i rhs_evens0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_evens);
  __m128i rhs_odds = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, rhs_shuffled0, __m128i);
  __m256i rhs_odds0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_odds);
  __m256i left =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_evens0, rhs_evens0);
  __m256i right =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_odds0, rhs_odds0);
  __m256i right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(right);
  __m256i right1 = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      right0,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          -(int32_t)zeta3, (int32_t)zeta3, -(int32_t)zeta2, (int32_t)zeta2,
          -(int32_t)zeta1, (int32_t)zeta1, -(int32_t)zeta0, (int32_t)zeta0));
  __m256i products_left = libcrux_intrinsics_avx2_mm256_add_epi32(left, right1);
  __m256i products_left0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_left);
  __m256i rhs_adjacent_swapped = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      rhs,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14, (int8_t)9, (int8_t)8,
          (int8_t)11, (int8_t)10, (int8_t)5, (int8_t)4, (int8_t)7, (int8_t)6,
          (int8_t)1, (int8_t)0, (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12,
          (int8_t)15, (int8_t)14, (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10,
          (int8_t)5, (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0,
          (int8_t)3, (int8_t)2));
  __m256i products_right =
      libcrux_intrinsics_avx2_mm256_madd_epi16(lhs, rhs_adjacent_swapped);
  __m256i products_right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_right);
  __m256i products_right1 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)16, products_right0, __m256i);
  return libcrux_intrinsics_avx2_mm256_blend_epi16((int32_t)170, products_left0,
                                                   products_right1, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_ntt_multiply_ea(
    __m256i *lhs, __m256i *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    __m256i vector, uint8_t ret[2U]) {
  __m256i lsb_to_msb =
      libcrux_intrinsics_avx2_mm256_slli_epi16((int32_t)15, vector, __m256i);
  __m128i low_msbs = libcrux_intrinsics_avx2_mm256_castsi256_si128(lsb_to_msb);
  __m128i high_msbs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, lsb_to_msb, __m128i);
  __m128i msbs = libcrux_intrinsics_avx2_mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = libcrux_intrinsics_avx2_mm_movemask_epi8(msbs);
  uint8_t serialized[2U] = {0U};
  serialized[0U] = (uint8_t)bits_packed;
  serialized[1U] = (uint8_t)(bits_packed >> 8U);
  memcpy(ret, serialized, (size_t)2U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_1_ea(__m256i vector,
                                                             uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_set_epi16(
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
  __m256i shift_lsb_to_msb = libcrux_intrinsics_avx2_mm256_set_epi16(
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768,
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768);
  __m256i coefficients_in_msb =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
  return libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)15,
                                                  coefficients_in_msb, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_1_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    __m256i vector, uint8_t ret[8U]) {
  uint8_t serialized[16U] = {0U};
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_madd_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set_epi16(
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
                  (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1));
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_2_combined,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4, (int8_t)0,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4, (int8_t)0));
  __m256i combined = libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
      adjacent_8_combined, libcrux_intrinsics_avx2_mm256_set_epi32(
                               (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
                               (int32_t)0, (int32_t)0, (int32_t)4, (int32_t)0));
  __m128i combined0 = libcrux_intrinsics_avx2_mm256_castsi256_si128(combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t), combined0);
  uint8_t ret0[8U];
  Result_56 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)8U, uint8_t),
      Eurydice_slice, uint8_t[8U]);
  unwrap_26_0e(dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_4_ea(__m256i vector,
                                                             uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_set_epi16(
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
  __m256i shift_lsbs_to_msbs = libcrux_intrinsics_avx2_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  __m256i coefficients_in_msb = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients, shift_lsbs_to_msbs);
  __m256i coefficients_in_lsb = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)4, coefficients_in_msb, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients_in_lsb, libcrux_intrinsics_avx2_mm256_set1_epi16(
                               ((int16_t)1 << 4U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_4_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    __m256i vector, uint8_t ret[10U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_madd_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set_epi16(
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
                  (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1));
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_2_combined,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22, (int32_t)0,
          (int32_t)22, (int32_t)0, (int32_t)22));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)22, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)8, adjacent_4_combined0, __m256i);
  __m256i adjacent_8_combined0 = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_8_combined,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12, (int32_t)0,
          (int32_t)0, (int32_t)0, (int32_t)12));
  __m256i adjacent_8_combined1 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)12, adjacent_8_combined0, __m256i);
  __m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined1);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  __m128i upper_8 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined1, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)5U, (size_t)21U, uint8_t),
      upper_8);
  uint8_t ret0[10U];
  Result_cd dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t),
      Eurydice_slice, uint8_t[10U]);
  unwrap_26_07(dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_5_ea(__m256i vector,
                                                             uint8_t ret[10U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes) {
  __m128i coefficients = libcrux_intrinsics_avx2_mm_set_epi8(
      Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *),
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
      libcrux_intrinsics_avx2_mm256_castsi128_si256(coefficients);
  __m256i coefficients_loaded0 = libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, coefficients_loaded, coefficients, __m256i);
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      coefficients_loaded0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)15, (int8_t)14, (int8_t)15, (int8_t)14, (int8_t)13,
          (int8_t)12, (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10,
          (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)9, (int8_t)8,
          (int8_t)7, (int8_t)6, (int8_t)7, (int8_t)6, (int8_t)5, (int8_t)4,
          (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)3, (int8_t)2,
          (int8_t)1, (int8_t)0, (int8_t)1, (int8_t)0));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients0, libcrux_intrinsics_avx2_mm256_set_epi16(
                         (int16_t)1 << 0U, (int16_t)1 << 5U, (int16_t)1 << 2U,
                         (int16_t)1 << 7U, (int16_t)1 << 4U, (int16_t)1 << 9U,
                         (int16_t)1 << 6U, (int16_t)1 << 11U, (int16_t)1 << 0U,
                         (int16_t)1 << 5U, (int16_t)1 << 2U, (int16_t)1 << 7U,
                         (int16_t)1 << 4U, (int16_t)1 << 9U, (int16_t)1 << 6U,
                         (int16_t)1 << 11U));
  return libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)11, coefficients1,
                                                  __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_5_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    __m256i vector, uint8_t ret[20U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_madd_epi16(
      vector,
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
          (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
          (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
          (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1));
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_2_combined,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12, (int32_t)0,
          (int32_t)12, (int32_t)0, (int32_t)12));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)12, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_4_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
          (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)4,
          (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  __m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  __m128i upper_8 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)10U, (size_t)26U,
                                  uint8_t),
      upper_8);
  uint8_t ret0[20U];
  Result_7a dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t),
      Eurydice_slice, uint8_t[20U]);
  unwrap_26_ea(dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_10_ea(
    __m256i vector, uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes) {
  __m256i shift_lsbs_to_msbs = libcrux_intrinsics_avx2_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients,
      libcrux_intrinsics_avx2_mm_set_epi8(9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U, 4U,
                                          3U, 3U, 2U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)4U, (size_t)20U, uint8_t));
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, libcrux_intrinsics_avx2_mm_set_epi8(
                              15U, 14U, 14U, 13U, 13U, 12U, 12U, 11U, 10U, 9U,
                              9U, 8U, 8U, 7U, 7U, 6U));
  __m256i coefficients =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients0);
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, coefficients, upper_coefficients0, __m256i);
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients0, shift_lsbs_to_msbs);
  __m256i coefficients2 = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)6, coefficients1, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients2, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 10U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_10_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    __m256i vector, uint8_t ret[22U]) {
  int16_t array[16U] = {0U};
  libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t), vector);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable_from_i16_array_0d(
          Eurydice_array_to_slice((size_t)16U, array, int16_t));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_11_0d(input, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_11_ea(
    __m256i vector, uint8_t ret[22U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_11_0d(bytes);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  return libcrux_intrinsics_avx2_mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_11_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    __m256i vector, uint8_t ret[24U]) {
  uint8_t serialized[32U] = {0U};
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_madd_epi16(
      vector,
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
          (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
          (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
          (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1));
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_2_combined, libcrux_intrinsics_avx2_mm256_set_epi32(
                               (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8,
                               (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)8, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_4_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13,
          (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)5,
          (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13, (int8_t)12,
          (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
          (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  __m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  __m128i upper_8 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)12U, (size_t)28U,
                                  uint8_t),
      upper_8);
  uint8_t ret0[24U];
  Result_6f dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)24U, uint8_t),
      Eurydice_slice, uint8_t[24U]);
  unwrap_26_76(dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_12_ea(
    __m256i vector, uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes) {
  __m256i shift_lsbs_to_msbs = libcrux_intrinsics_avx2_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients,
      libcrux_intrinsics_avx2_mm_set_epi8(11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U, 5U,
                                          4U, 4U, 3U, 2U, 1U, 1U, 0U));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(bytes, (size_t)8U, (size_t)24U, uint8_t));
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients,
      libcrux_intrinsics_avx2_mm_set_epi8(15U, 14U, 14U, 13U, 12U, 11U, 11U,
                                          10U, 9U, 8U, 8U, 7U, 6U, 5U, 5U, 4U));
  __m256i coefficients =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients0);
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, coefficients, upper_coefficients0, __m256i);
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients0, shift_lsbs_to_msbs);
  __m256i coefficients2 = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)4, coefficients1, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients2, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 12U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_deserialize_12_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_avx2_sampling_rejection_sample(Eurydice_slice input,
                                                     Eurydice_slice output) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i potential_coefficients =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_12(input);
  __m256i compare_with_field_modulus =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi16(field_modulus,
                                                potential_coefficients);
  uint8_t good[2U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(compare_with_field_modulus,
                                                   good);
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[0U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(potential_coefficients);
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8_6__count_ones(good[0U]);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[1U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, potential_coefficients, __m128i);
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)8U, int16_t),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8_6__count_ones(good[1U]);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline size_t libcrux_ml_kem_vector_avx2_rej_sample_ea(
    Eurydice_slice input, Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_ZERO_d6_7d(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 lit;
  lit.coefficients[0U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[1U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[2U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[3U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[4U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[5U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[6U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[7U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[8U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[9U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[10U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[11U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[12U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[13U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[14U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  lit.coefficients[15U] = libcrux_ml_kem_vector_avx2_ZERO_ea();
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_deserialize_secret_key_closure_77(size_t _) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_2e(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_deserialize_secret_key_9c(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    secret_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
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
        libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_2e(
            secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_closure_4b(size_t _) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_21(
    __m256i vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)10);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)10, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)10, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_21(
      vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_10_a5(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be(
            coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_210(
    __m256i vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)11);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)11, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)11, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 11
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be0(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_210(
      vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_11_83(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be0(
            coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_31(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_10_a5(serialized);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_traits_montgomery_multiply_fe_71(
    __m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
libcrux_ml_kem_ntt_ntt_layer_int_vec_step_24(__m256i a, __m256i b,
                                             int16_t zeta_r) {
  __m256i t = libcrux_ml_kem_vector_traits_montgomery_multiply_fe_71(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_ea(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_ea(a, &t);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t layer, size_t _initial_coefficient_bound) {
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
          libcrux_ml_kem_ntt_ntt_layer_int_vec_step_24(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_3_c0(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(
        re->coefficients[round],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_2_9a(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(
        re->coefficients[round],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                           (size_t)1U]);
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_1_03(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(
        re->coefficients[round],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                           (size_t)1U],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                           (size_t)2U],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                           (size_t)3U]);
    zeta_i[0U] = zeta_i[0U] + (size_t)3U;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_5c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    self->coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_ea(self->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_vector_u_7a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)7U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)6U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)5U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)4U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_c0(&zeta_i, re, (size_t)3U, (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_9a(&zeta_i, re, (size_t)2U, (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_03(&zeta_i, re, (size_t)1U, (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_5c(re);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_f2(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    u_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
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
    u_as_ntt[i0] =
        libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_31(
            u_bytes);
    libcrux_ml_kem_ntt_ntt_vector_u_7a(&u_as_ntt[i0]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_211(
    __m256i vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)4);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)4, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)4, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be1(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_211(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_4_a9(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be1(
            coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_212(
    __m256i vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)5);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)5, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)5, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 5
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be2(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_212(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_5_22(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_ea_be2(
            re.coefficients[i0]);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_15(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_4_a9(serialized);
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
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_ntt_multiply_d6_c4(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    out.coefficients[i0] = libcrux_ml_kem_vector_avx2_ntt_multiply_ea(
        &self->coefficients[i0], &rhs->coefficients[i0],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[(size_t)64U +
                                                           (size_t)4U * i0],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[(size_t)64U +
                                                           (size_t)4U * i0 +
                                                           (size_t)1U],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[(size_t)64U +
                                                           (size_t)4U * i0 +
                                                           (size_t)2U],
        libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[(size_t)64U +
                                                           (size_t)4U * i0 +
                                                           (size_t)3U]);
  }
  return out;
}

/**
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
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_d6_86(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, self->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_ea(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_2b(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(
            re->coefficients[round],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                               (size_t)1U],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                               (size_t)2U],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                               (size_t)3U]);
    zeta_i[0U] = zeta_i[0U] - (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_08(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(
            re->coefficients[round],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                               (size_t)1U]);
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_22(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(
            re->coefficients[round],
            libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_c7(__m256i a,
                                                               __m256i b,
                                                               int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_ea(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
      libcrux_ml_kem_vector_avx2_add_ea(a, &b));
  b = libcrux_ml_kem_vector_traits_montgomery_multiply_fe_71(a_minus_b, zeta_r);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_6d(
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
          libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_c7(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_66(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_2b(&zeta_i, re, (size_t)1U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_08(&zeta_i, re, (size_t)2U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_22(&zeta_i, re, (size_t)3U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_6d(&zeta_i, re,
                                                          (size_t)4U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_6d(&zeta_i, re,
                                                          (size_t)5U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_6d(&zeta_i, re,
                                                          (size_t)6U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_6d(&zeta_i, re,
                                                          (size_t)7U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_5c(re);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_subtract_reduce_d6_7f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            b.coefficients[i0], (int16_t)1441);
    b.coefficients[i0] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_sub_ea(self->coefficients[i0],
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_message_ad(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
        libcrux_ml_kem_polynomial_ntt_multiply_d6_c4(&secret_as_ntt[i0],
                                                     &u_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_86(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_66(&result);
  result = libcrux_ml_kem_polynomial_subtract_reduce_d6_7f(v, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_shift_right_6e(__m256i vector) {
  return libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, vector, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.shift_right_ea
with const generics
- SHIFT_BY= 15
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_shift_right_ea_32(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_shift_right_6e(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_vector_traits_to_unsigned_representative_09(__m256i a) {
  __m256i t = libcrux_ml_kem_vector_avx2_shift_right_ea_32(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_ea(a, &fm);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_message_38(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    __m256i coefficient =
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re.coefficients[i0]);
    __m256i coefficient_compressed =
        libcrux_ml_kem_vector_avx2_compress_1_ea(coefficient);
    uint8_t bytes[2U];
    libcrux_ml_kem_vector_avx2_serialize_1_ea(coefficient_compressed, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)2U * i0, (size_t)2U * i0 + (size_t)2U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)2U, bytes, uint8_t), uint8_t);
  }
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_decrypt_unpacked_f0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_f2(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_15(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      libcrux_ml_kem_matrix_compute_message_ad(&v, secret_key->secret_as_ntt,
                                               u_as_ntt);
  uint8_t ret0[32U];
  libcrux_ml_kem_serialize_compress_then_serialize_message_38(message, ret0);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_decrypt_5c(Eurydice_slice secret_key,
                                                     uint8_t *ciphertext,
                                                     uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  libcrux_ml_kem_ind_cpa_deserialize_secret_key_9c(secret_key, secret_as_ntt);
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
  uint8_t ret0[32U];
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_f0(&secret_key_unpacked, ciphertext,
                                             ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G_a9_67(
    Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_d1(
    Eurydice_slice input, uint8_t ret[32U]) {
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_a9_42(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_PRF_d1(input, ret);
}

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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_default_8d_20(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    uu____0[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  lit.A[0U][0U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[0U][1U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[0U][2U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[1U][0U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[1U][1U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[1U][2U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[2U][0U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[2U][1U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.A[2U][2U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_f6(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(coefficient);
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
- PUBLIC_KEY_SIZE= 1152
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_6d(
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
        libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_f6(
            ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

typedef libcrux_sha3_avx2_x4_incremental_KeccakState
    libcrux_ml_kem_hash_functions_avx2_Simd256Hash;

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_2a(
    uint8_t input[3U][34U]) {
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
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_a9 with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_a9_1c(
    uint8_t input[3U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[3U][34U];
  memcpy(copy_of_input, input, (size_t)3U * sizeof(uint8_t[34U]));
  return libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_2a(
      copy_of_input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_three_blocks with const
generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_three_blocks_0c(
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
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_three_blocks_a9 with const
generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_three_blocks_a9_2e(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_three_blocks_0c(self,
                                                                      ret);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_b8(
    uint8_t randomness[3U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients[i1] <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice uu____0 =
            Eurydice_array_to_subslice2(randomness[i1], r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U, uint8_t);
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
            uu____0, Eurydice_array_to_subslice2(
                         out[i1], sampled_coefficients[i1],
                         sampled_coefficients[i1] + (size_t)16U, int16_t));
        size_t uu____1 = i1;
        sampled_coefficients[uu____1] = sampled_coefficients[uu____1] + sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (sampled_coefficients[i0] >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients[i0] =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_block with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_block_4a(
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
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_block_a9 with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_block_a9_1d(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_block_4a(self, ret);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_b80(
    uint8_t randomness[3U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients[i1] <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        Eurydice_slice uu____0 =
            Eurydice_array_to_subslice2(randomness[i1], r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U, uint8_t);
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
            uu____0, Eurydice_array_to_subslice2(
                         out[i1], sampled_coefficients[i1],
                         sampled_coefficients[i1] + (size_t)16U, int16_t));
        size_t uu____1 = i1;
        sampled_coefficients[uu____1] = sampled_coefficients[uu____1] + sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (sampled_coefficients[i0] >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients[i0] =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_from_i16_array_d6_df(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice_subslice2(
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_xof_closure_f9(int16_t s[272U]) {
  return libcrux_ml_kem_polynomial_from_i16_array_d6_df(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_a3(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[3U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_a9_1c(
          copy_of_seeds);
  uint8_t randomness0[3U][504U];
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_three_blocks_a9_2e(
      &xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[3U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_b8(
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_block_a9_1d(
          &xof_state, randomness);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[3U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)3U * sizeof(uint8_t[168U]));
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_b80(
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret0[i] =
        libcrux_ml_kem_sampling_sample_from_xof_closure_f9(copy_of_out[i]);
  }
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_8e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*A_transpose)[3U],
    uint8_t seed[34U], bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_seed[34U];
    memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
    uint8_t seeds[3U][34U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t));
    }
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds[j][32U] = (uint8_t)i1;
      seeds[j][33U] = (uint8_t)j;
    }
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_seeds[3U][34U];
    memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[3U];
    libcrux_ml_kem_sampling_sample_from_xof_a3(copy_of_seeds, sampled);
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
  }
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[3size_t], uint8_t

*/
typedef struct tuple_b00_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 fst[3U];
  uint8_t snd;
} tuple_b00;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt_out.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_out_closure_36(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN_08(
    uint8_t (*input)[33U], uint8_t ret[3U][128U]) {
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_16(
    uint8_t (*input)[33U], uint8_t ret[3U][128U]) {
  libcrux_ml_kem_hash_functions_avx2_PRFxN_08(input, ret);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_43(
    Eurydice_slice randomness) {
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
  return libcrux_ml_kem_polynomial_from_i16_array_d6_df(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_binomial_distribution_3_a0(
    Eurydice_slice randomness) {
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
  return libcrux_ml_kem_polynomial_from_i16_array_d6_df(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_binomial_distribution_29(
    Eurydice_slice randomness) {
  return libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_43(
      randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_7_c8(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
        re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_avx2_sub_ea(re->coefficients[j], &t);
    re->coefficients[j] =
        libcrux_ml_kem_vector_avx2_add_ea(re->coefficients[j], &t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_7b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  libcrux_ml_kem_ntt_ntt_at_layer_7_c8(re);
  size_t zeta_i = (size_t)1U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)6U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)5U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_48(&zeta_i, re, (size_t)4U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_c0(&zeta_i, re, (size_t)3U, (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_9a(&zeta_i, re, (size_t)2U, (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_03(&zeta_i, re, (size_t)1U, (size_t)3U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_5c(re);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_5f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re_as_ntt,
    uint8_t prf_input[33U], uint8_t domain_separator) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs[i0][32U] = domain_separator;
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  uint8_t prf_outputs[3U][128U];
  libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_16(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    re_as_ntt[i0] =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_29(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_7b(&re_as_ntt[i0]);
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt_out
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE tuple_b00
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_out_35(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    re_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = re_as_ntt;
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  domain_separator = libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_5f(
      uu____0, uu____1, domain_separator);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[3U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 lit;
  memcpy(
      lit.fst, copy_of_re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_closure_eb(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE tuple_b00
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_ef(uint8_t prf_input[33U],
                                                  uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    error_1[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs[i0][32U] = domain_separator;
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  uint8_t prf_outputs[3U][128U];
  libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_16(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_29(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    error_1[i0] = uu____1;
  }
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[3U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 lit;
  memcpy(
      lit.fst, copy_of_error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_d10(
    Eurydice_slice input, uint8_t ret[128U]) {
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_a9_420(
    Eurydice_slice input, uint8_t ret[128U]) {
  libcrux_ml_kem_hash_functions_avx2_PRF_d10(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_vector_u_closure_77(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_d6_7f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            self->coefficients[j], (int16_t)1441);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form,
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_vector_u_2b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    result[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
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
          libcrux_ml_kem_polynomial_ntt_multiply_d6_c4(a_element, &r_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_86(&result[i1],
                                                          &product);
    }
    libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_66(&result[i1]);
    libcrux_ml_kem_polynomial_add_error_reduce_d6_7f(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_traits_decompress_1_68(__m256i v) {
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
      libcrux_ml_kem_vector_avx2_sub_ea(libcrux_ml_kem_vector_avx2_ZERO_ea(),
                                        &v),
      (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_message_84(
    uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    __m256i coefficient_compressed =
        libcrux_ml_kem_vector_avx2_deserialize_1_ea(
            Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                        (size_t)2U * i0 + (size_t)2U, uint8_t));
    re.coefficients[i0] =
        libcrux_ml_kem_vector_traits_decompress_1_68(coefficient_compressed);
  }
  return re;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_add_message_error_reduce_d6_93(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            result.coefficients[i0], (int16_t)1441);
    __m256i tmp = libcrux_ml_kem_vector_avx2_add_ea(self->coefficients[i0],
                                                    &message->coefficients[i0]);
    __m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form, &tmp);
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_ea(tmp0);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_ring_element_v_3c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_d6_7d();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
        libcrux_ml_kem_polynomial_ntt_multiply_d6_c4(&t_as_ntt[i0],
                                                     &r_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_86(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_66(&result);
  result = libcrux_ml_kem_polynomial_add_message_error_reduce_d6_93(
      error_2, message, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_03(
    __m256i vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)10) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)10, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)10, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_compress_ea_09(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_03(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_10_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = libcrux_ml_kem_vector_avx2_compress_ea_09(
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2_serialize_10_ea(coefficient, bytes);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_030(
    __m256i vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)11) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)11, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)11, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 11
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_compress_ea_090(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_030(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_11_72(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = libcrux_ml_kem_vector_avx2_compress_ea_090(
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2_serialize_11_ea(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)22U * i0, (size_t)22U * i0 + (size_t)22U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)22U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_75(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  libcrux_ml_kem_serialize_compress_then_serialize_10_1b(re, uu____0);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_compress_then_serialize_u_df(
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
    libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_75(&re,
                                                                       ret);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_031(
    __m256i vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)4) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)4, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)4, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_compress_ea_091(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_031(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_4_c3(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = libcrux_ml_kem_vector_avx2_compress_ea_091(
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_ea(coefficient, bytes);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_032(
    __m256i vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)5) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)5, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector, __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)5, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64((int32_t)216,
                                                         compressed, __m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 5
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_compress_ea_092(
    __m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_032(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_5_49(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficients = libcrux_ml_kem_vector_avx2_compress_ea_092(
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_ea(coefficients, bytes);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_94(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  libcrux_ml_kem_serialize_compress_then_serialize_4_c3(re, out);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_encrypt_unpacked_c1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_422(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____1 = libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_out_35(
      copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____3 = libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_ef(
      copy_of_prf_input, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_420(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t), prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      libcrux_ml_kem_sampling_sample_from_binomial_distribution_29(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  libcrux_ml_kem_matrix_compute_vector_u_2b(public_key->A, r_as_ntt, error_1,
                                            u);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      libcrux_ml_kem_serialize_deserialize_then_decompress_message_84(
          copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      libcrux_ml_kem_matrix_compute_ring_element_v_3c(
          public_key->t_as_ntt, r_as_ntt, &error_2, &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_compress_then_serialize_u_df(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_94(
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_encrypt_e2(Eurydice_slice public_key,
                                                     uint8_t message[32U],
                                                     Eurydice_slice randomness,
                                                     uint8_t ret[1088U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_8d_20();
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_6d(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t),
      unpacked_public_key.t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____0)[3U] =
      unpacked_public_key.A;
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_421(seed, ret0);
  libcrux_ml_kem_matrix_sample_matrix_A_8e(uu____0, ret0, false);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____1 =
      &unpacked_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_c1(uu____1, copy_of_message,
                                             randomness, ret1);
  memcpy(ret, ret1, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_kdf_d8_eb(
    Eurydice_slice shared_secret, libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_,
    uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_decapsulate_22(
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
  libcrux_ml_kem_ind_cpa_decrypt_5c(ind_cpa_secret_key, ciphertext->value,
                                    decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_420(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_42(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_e2(uu____5, copy_of_decrypted,
                                    pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_variant_kdf_d8_eb(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t),
      ciphertext, implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_variant_kdf_d8_eb(shared_secret0, ciphertext, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 Portable decapsulate
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_17(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_22(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_17(private_key,
                                                            ciphertext, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_entropy_preprocess_d8_0a(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H_a9_16(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
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
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_encapsulate_25(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  libcrux_ml_kem_variant_entropy_preprocess_d8_0a(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_ba_c1(public_key),
                              uint8_t),
      ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_ba_c1(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_e2(uu____2, copy_of_randomness,
                                    pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_fc_89(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  libcrux_ml_kem_variant_kdf_d8_eb(shared_secret, &ciphertext0,
                                   shared_secret_array);
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
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate
with const generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c
libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_9b(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_25(uu____0, copy_of_randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_mlkem768_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_9b(
      uu____0, copy_of_randomness);
}

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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_default_1a_bf(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 lit;
  lit.secret_as_ntt[0U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.secret_as_ntt[1U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  lit.secret_as_ntt[2U] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_d8
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_cpa_keygen_seed_d8_48(
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
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_traits_to_standard_domain_ba(
    __m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_4e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_traits_to_standard_domain_ba(
            self->coefficients[j]);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form,
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_As_plus_e_91(
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        libcrux_ml_kem_polynomial_ZERO_d6_7d();
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
          libcrux_ml_kem_polynomial_ntt_multiply_d6_c4(matrix_element,
                                                       &s_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_86(&t_as_ntt[i0],
                                                          &product);
    }
    libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_4e(
        &t_as_ntt[i0], &error_as_ntt[i0]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_35(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  libcrux_ml_kem_variant_cpa_keygen_seed_d8_48(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_A, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_8e(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_5f(
          uu____2, copy_of_prf_input0, 0U);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_out_35(
          copy_of_prf_input, domain_separator)
          .fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_matrix_compute_As_plus_e_91(
      public_key->t_as_ntt, public_key->A, private_key->secret_as_ntt,
      error_as_ntt);
  uint8_t uu____5[32U];
  Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_a3(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        libcrux_ml_kem_vector_traits_to_unsigned_representative_09(
            re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2_serialize_12_ea(coefficient, bytes);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_secret_key_17(
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
    libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_a3(&re, ret0);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_mut_34(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                       (size_t)1152U, uint8_t);
  uint8_t ret[1152U];
  libcrux_ml_kem_ind_cpa_serialize_secret_key_17(t_as_ntt, ret);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_3b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_34(t_as_ntt, seed_for_a,
                                                     public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_utils_extraction_helper_Keypair768
libcrux_ml_kem_ind_cpa_generate_keypair_31(Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 private_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_1a_bf();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 public_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_8d_20();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_35(
      key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_3b(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  libcrux_ml_kem_ind_cpa_serialize_secret_key_17(private_key.secret_as_ntt,
                                                 secret_key_serialized);
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
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_7a(
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
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(public_key, ret0);
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
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_cb(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      libcrux_ml_kem_ind_cpa_generate_keypair_31(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_7a(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_88_58(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_dc(
      uu____2, libcrux_ml_kem_types_from_40_cb(copy_of_public_key));
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_83(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_cb(copy_of_randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_avx2_generate_key_pair(uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_83(
      copy_of_randomness);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::Kyber)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_33
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_kdf_33_9d(
    Eurydice_slice shared_secret,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t kdf_input[64U];
  libcrux_ml_kem_utils_into_padded_array_42(shared_secret, kdf_input);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, kdf_input, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_slice((size_t)1088U,
                              libcrux_ml_kem_types_as_slice_07_46(ciphertext),
                              uint8_t),
      ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t ret1[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_42(
      Eurydice_array_to_slice((size_t)64U, kdf_input, uint8_t), ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_Kyber
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_decapsulate_220(
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
  libcrux_ml_kem_ind_cpa_decrypt_5c(ind_cpa_secret_key, ciphertext->value,
                                    decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_420(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_42(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_e2(uu____5, copy_of_decrypted,
                                    pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_variant_kdf_33_9d(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t),
      ciphertext, implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_variant_kdf_33_9d(shared_secret0, ciphertext, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.kyber_decapsulate with const generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_decapsulate_7f(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_220(private_key, ciphertext, ret);
}

/**
 Decapsulate Kyber 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_kyber_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_decapsulate_7f(
      private_key, ciphertext, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::Kyber)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_33
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_entropy_preprocess_33_4e(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(randomness, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_Kyber
with const generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_encapsulate_250(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  libcrux_ml_kem_variant_entropy_preprocess_33_4e(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_ba_c1(public_key),
                              uint8_t),
      ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_ba_c1(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_e2(uu____2, copy_of_randomness,
                                    pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_fc_89(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  libcrux_ml_kem_variant_kdf_33_9d(shared_secret, &ciphertext0,
                                   shared_secret_array);
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
 Portable encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.kyber_encapsulate with const generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c
libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_encapsulate_21(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_250(uu____0, copy_of_randomness);
}

/**
 Encapsulate Kyber 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_mlkem768_avx2_kyber_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_encapsulate_21(
      uu____0, copy_of_randomness);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::Kyber)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_33
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_cpa_keygen_seed_33_50(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(key_generation_seed, ret);
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
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_Kyber
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_350(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  libcrux_ml_kem_variant_cpa_keygen_seed_33_50(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_421(seed_for_A, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_8e(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_422(seed_for_secret_and_error,
                                             prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____2 =
      private_key->secret_as_ntt;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t domain_separator =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_5f(
          uu____2, copy_of_prf_input0, 0U);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_out_35(
          copy_of_prf_input, domain_separator)
          .fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_matrix_compute_As_plus_e_91(
      public_key->t_as_ntt, public_key->A, private_key->secret_as_ntt,
      error_as_ntt);
  uint8_t uu____5[32U];
  Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U]);
  unwrap_26_33(dst, uu____5);
  memcpy(public_key->seed_for_A, uu____5, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_Kyber
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_utils_extraction_helper_Keypair768
libcrux_ml_kem_ind_cpa_generate_keypair_310(
    Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 private_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_1a_bf();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 public_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_8d_20();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_350(
      key_generation_seed, &private_key, &public_key);
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_3b(
      public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  libcrux_ml_kem_ind_cpa_serialize_secret_key_17(private_key.secret_as_ntt,
                                                 secret_key_serialized);
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
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_Kyber
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_cb0(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      libcrux_ml_kem_ind_cpa_generate_keypair_310(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_7a(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_88_58(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_dc(
      uu____2, libcrux_ml_kem_types_from_40_cb(copy_of_public_key));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.kyber_generate_keypair with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_generate_keypair_d8(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_cb0(copy_of_randomness);
}

/**
 Generate Kyber 768 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_avx2_kyber_generate_key_pair(uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_generate_keypair_d8(
      copy_of_randomness);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_ce(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  uint8_t t[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_subslice2(private_key->value, (size_t)384U * (size_t)3U,
                                  (size_t)768U * (size_t)3U + (size_t)32U,
                                  uint8_t),
      t);
  Eurydice_slice expected = Eurydice_array_to_subslice2(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t);
  return core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq(
      (size_t)32U, t, &expected, uint8_t, uint8_t, bool);
}

/**
 Portable private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_00(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_ce(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem768_avx2_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_00(
      private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.closure with
types libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1184
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_out_closure_01(
    size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1184
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_6d0(
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
        libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_f6(
            ring_element);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_out_c5(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    deserialized_pk[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_6d0(
      public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_public_key_8f(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_out_c5(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_3b(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
 Portable public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_7c(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_8f(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem768_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_7c(
      public_key->value);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_decapsulate_1c(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_f0(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
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
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_420(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_42(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_c1(
      uu____3, copy_of_decrypted, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_fd_89(ciphertext),
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
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.decapsulate with const
generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_87(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_1c(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_decapsulate(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_87(
      private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_unpacked_encapsulate_5f(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_42(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  Eurydice_slice_copy(uu____0,
                      Eurydice_array_to_slice(
                          (size_t)32U, public_key->public_key_hash, uint8_t),
                      uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_67(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
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
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_c1(uu____2, copy_of_randomness,
                                             pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types_from_fc_89(copy_of_ciphertext);
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
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.encapsulate with const
generics
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_f7(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_5f(uu____0,
                                                        copy_of_randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_mlkem768_avx2_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_f7(
      uu____0, copy_of_randomness);
}

/**
 Read the bytes into an unpacked key pair.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.from_bytes_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_from_bytes_dd_96(Eurydice_slice bytes) {
  size_t p = (size_t)0U;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      ind_cpa_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_8d_20();
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, ind_cpa_public_key.t_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)16U, ind_cpa_public_key.t_as_ntt[i1].coefficients,
                     __m256i),
                 __m256i);
         i++) {
      size_t j = i;
      ind_cpa_public_key.t_as_ntt[i1].coefficients[j] =
          libcrux_ml_kem_vector_avx2_from_bytes_ea(
              Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t));
      p = p + (size_t)32U;
    }
  }
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t),
      Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t), uint8_t);
  p = p + (size_t)32U;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, ind_cpa_public_key.A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]);
       i0++) {
    size_t i1 = i0;
    for (size_t i2 = (size_t)0U;
         i2 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, ind_cpa_public_key.A[i1],
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i2++) {
      size_t j = i2;
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)16U, ind_cpa_public_key.A[i1][j].coefficients,
                       __m256i),
                   __m256i);
           i++) {
        size_t k = i;
        ind_cpa_public_key.A[i1][j].coefficients[k] =
            libcrux_ml_kem_vector_avx2_from_bytes_ea(
                Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t));
        p = p + (size_t)32U;
      }
    }
  }
  uint8_t public_key_hash[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, public_key_hash, uint8_t),
      Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t), uint8_t);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 uu____0 =
      ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_hash[32U];
  memcpy(copy_of_public_key_hash, public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key = uu____0;
  memcpy(lit.public_key_hash, copy_of_public_key_hash,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Read the bytes into an unpacked key pair.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.from_bytes_f8
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_from_bytes_f8_c2(Eurydice_slice bytes) {
  size_t p = (size_t)0U;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key = libcrux_ml_kem_ind_cpa_unpacked_default_1a_bf();
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, ind_cpa_private_key.secret_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(
             Eurydice_array_to_slice(
                 (size_t)16U,
                 ind_cpa_private_key.secret_as_ntt[i1].coefficients, __m256i),
             __m256i);
         i++) {
      size_t j = i;
      ind_cpa_private_key.secret_as_ntt[i1].coefficients[j] =
          libcrux_ml_kem_vector_avx2_from_bytes_ea(
              Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t));
      p = p + (size_t)32U;
    }
  }
  uint8_t implicit_rejection_value[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_value, uint8_t),
      Eurydice_slice_subslice2(bytes, p, p + (size_t)32U, uint8_t), uint8_t);
  p = p + (size_t)32U;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 public_key =
      libcrux_ml_kem_ind_cca_unpacked_from_bytes_dd_96(
          Eurydice_slice_subslice_from(bytes, p, uint8_t, size_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 uu____0 =
      ind_cpa_private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_implicit_rejection_value[32U];
  memcpy(copy_of_implicit_rejection_value, implicit_rejection_value,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked lit;
  lit.private_key.ind_cpa_private_key = uu____0;
  memcpy(lit.private_key.implicit_rejection_value,
         copy_of_implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  lit.public_key = public_key;
  return lit;
}

/**
 Read bytes into the key pair.

 `bytes` has to point to at least 7776 bytes.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_avx2_unpacked_from_bytes(Eurydice_slice bytes) {
  return libcrux_ml_kem_ind_cca_unpacked_from_bytes_f8_c2(bytes);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair.closure.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_closure_closure_0c(size_t _j) {
  return libcrux_ml_kem_polynomial_ZERO_d6_7d();
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_closure_0d(
    size_t _i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret[i] = libcrux_ml_kem_polynomial_ZERO_d6_7d();
  }
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_17
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_clone_17_e6(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 lit;
  __m256i ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret, __m256i, void *);
  memcpy(lit.coefficients, ret, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_a0(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_35(
      ind_cpa_keypair_randomness, &out->private_key.ind_cpa_private_key,
      &out->public_key.ind_cpa_public_key);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    libcrux_ml_kem_ind_cca_unpacked_generate_keypair_closure_0d(i, A[i]);
  }
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
          libcrux_ml_kem_polynomial_clone_17_e6(
              &out->public_key.ind_cpa_public_key.A[j][i1]);
      A[i1][j] = uu____0;
    }
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1[3U][3U];
  memcpy(uu____1, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(out->public_key.ind_cpa_public_key.A, uu____1,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t pk_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_3b(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      pk_serialized);
  uint8_t uu____2[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t), uu____2);
  memcpy(out->public_key.public_key_hash, uu____2,
         (size_t)32U * sizeof(uint8_t));
  uint8_t uu____3[32U];
  Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U]);
  unwrap_26_33(dst, uu____3);
  memcpy(out->private_key.implicit_rejection_value, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.generate_keypair with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_8b(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_a0(copy_of_randomness, out);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_generate_key_pair(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_8b(
      copy_of_randomness, key_pair);
}

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_82
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_default_82_aa(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_8d_20();
  lit.public_key_hash[0U] = 0U;
  lit.public_key_hash[1U] = 0U;
  lit.public_key_hash[2U] = 0U;
  lit.public_key_hash[3U] = 0U;
  lit.public_key_hash[4U] = 0U;
  lit.public_key_hash[5U] = 0U;
  lit.public_key_hash[6U] = 0U;
  lit.public_key_hash[7U] = 0U;
  lit.public_key_hash[8U] = 0U;
  lit.public_key_hash[9U] = 0U;
  lit.public_key_hash[10U] = 0U;
  lit.public_key_hash[11U] = 0U;
  lit.public_key_hash[12U] = 0U;
  lit.public_key_hash[13U] = 0U;
  lit.public_key_hash[14U] = 0U;
  lit.public_key_hash[15U] = 0U;
  lit.public_key_hash[16U] = 0U;
  lit.public_key_hash[17U] = 0U;
  lit.public_key_hash[18U] = 0U;
  lit.public_key_hash[19U] = 0U;
  lit.public_key_hash[20U] = 0U;
  lit.public_key_hash[21U] = 0U;
  lit.public_key_hash[22U] = 0U;
  lit.public_key_hash[23U] = 0U;
  lit.public_key_hash[24U] = 0U;
  lit.public_key_hash[25U] = 0U;
  lit.public_key_hash[26U] = 0U;
  lit.public_key_hash[27U] = 0U;
  lit.public_key_hash[28U] = 0U;
  lit.public_key_hash[29U] = 0U;
  lit.public_key_hash[30U] = 0U;
  lit.public_key_hash[31U] = 0U;
  return lit;
}

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_ec
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
    libcrux_ml_kem_ind_cca_unpacked_default_ec_f0(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____0;
  uu____0.ind_cpa_private_key = libcrux_ml_kem_ind_cpa_unpacked_default_1a_bf();
  uu____0.implicit_rejection_value[0U] = 0U;
  uu____0.implicit_rejection_value[1U] = 0U;
  uu____0.implicit_rejection_value[2U] = 0U;
  uu____0.implicit_rejection_value[3U] = 0U;
  uu____0.implicit_rejection_value[4U] = 0U;
  uu____0.implicit_rejection_value[5U] = 0U;
  uu____0.implicit_rejection_value[6U] = 0U;
  uu____0.implicit_rejection_value[7U] = 0U;
  uu____0.implicit_rejection_value[8U] = 0U;
  uu____0.implicit_rejection_value[9U] = 0U;
  uu____0.implicit_rejection_value[10U] = 0U;
  uu____0.implicit_rejection_value[11U] = 0U;
  uu____0.implicit_rejection_value[12U] = 0U;
  uu____0.implicit_rejection_value[13U] = 0U;
  uu____0.implicit_rejection_value[14U] = 0U;
  uu____0.implicit_rejection_value[15U] = 0U;
  uu____0.implicit_rejection_value[16U] = 0U;
  uu____0.implicit_rejection_value[17U] = 0U;
  uu____0.implicit_rejection_value[18U] = 0U;
  uu____0.implicit_rejection_value[19U] = 0U;
  uu____0.implicit_rejection_value[20U] = 0U;
  uu____0.implicit_rejection_value[21U] = 0U;
  uu____0.implicit_rejection_value[22U] = 0U;
  uu____0.implicit_rejection_value[23U] = 0U;
  uu____0.implicit_rejection_value[24U] = 0U;
  uu____0.implicit_rejection_value[25U] = 0U;
  uu____0.implicit_rejection_value[26U] = 0U;
  uu____0.implicit_rejection_value[27U] = 0U;
  uu____0.implicit_rejection_value[28U] = 0U;
  uu____0.implicit_rejection_value[29U] = 0U;
  uu____0.implicit_rejection_value[30U] = 0U;
  uu____0.implicit_rejection_value[31U] = 0U;
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked){
          .private_key = uu____0,
          .public_key = libcrux_ml_kem_ind_cca_unpacked_default_82_aa()});
}

/**
 Create a new, empty unpacked key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_avx2_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_ec_f0();
}

/**
 Create a new, empty unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_mlkem768_avx2_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_82_aa();
}

/**
 Read the key pair from `bytes``.

 `bytes` has to point to at least 7776 bytes.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_from_bytes(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_ind_cca_unpacked_from_bytes_f8_c2(bytes);
}

/**
 Get the serialized public key.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_ba with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_ba_74(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self,
    libcrux_ml_kem_types_MlKemPublicKey_15 *serialized) {
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_34(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized->value);
}

/**
 Get the serialized public key.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_fc with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_fc_09(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_15 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_ba_74(
      &self->public_key, serialized);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPublicKey_15 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_fc_09(key_pair,
                                                                  serialized);
}

/**
 Write the key into the `out` buffer.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.to_bytes_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_to_bytes_dd_75(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self,
    Eurydice_slice out) {
  size_t p = (size_t)0U;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, self->ind_cpa_public_key.t_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t =
        &self->ind_cpa_public_key.t_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)16U, t->coefficients, __m256i),
                 __m256i);
         i++) {
      size_t j = i;
      libcrux_ml_kem_vector_avx2_to_bytes_ea(
          t->coefficients[j],
          Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t));
      p = p + (size_t)32U;
    }
  }
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t),
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      uint8_t);
  p = p + (size_t)32U;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, self->ind_cpa_public_key.A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a1 =
        self->ind_cpa_public_key.A[i1];
    for (size_t i2 = (size_t)0U;
         i2 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, a1,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
         i2++) {
      size_t j = i2;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 a = a1[j];
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice(
                                      (size_t)16U, a.coefficients, __m256i),
                                  __m256i);
           i++) {
        size_t k = i;
        libcrux_ml_kem_vector_avx2_to_bytes_ea(
            a.coefficients[k],
            Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t));
        p = p + (size_t)32U;
      }
    }
  }
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t),
      Eurydice_array_to_slice((size_t)32U, self->public_key_hash, uint8_t),
      uint8_t);
}

/**
 Write the key into the `out` buffer.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.to_bytes_f8
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_to_bytes_f8_b1(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    Eurydice_slice out) {
  size_t p = (size_t)0U;
  for (size_t i0 = (size_t)0U;
       i0 <
       Eurydice_slice_len(
           Eurydice_array_to_slice(
               (size_t)3U, self->private_key.ind_cpa_private_key.secret_as_ntt,
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2),
           libcrux_ml_kem_polynomial_PolynomialRingElement_d2);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s =
        &self->private_key.ind_cpa_private_key.secret_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)16U, s->coefficients, __m256i),
                 __m256i);
         i++) {
      size_t j = i;
      libcrux_ml_kem_vector_avx2_to_bytes_ea(
          s->coefficients[j],
          Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t));
      p = p + (size_t)32U;
    }
  }
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(out, p, p + (size_t)32U, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      uint8_t);
  p = p + (size_t)32U;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      &self->public_key;
  libcrux_ml_kem_ind_cca_unpacked_to_bytes_dd_75(
      uu____0, Eurydice_slice_subslice_from(out, p, uint8_t, size_t));
}

/**
 Write out the key pair.

 `out` has to point to at least 7776 bytes.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_to_bytes(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_slice out) {
  libcrux_ml_kem_ind_cca_unpacked_to_bytes_f8_b1(key_pair, out);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2])#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_ef
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_clone_ef_f5(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)3U, self->t_as_ntt, uu____0,
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2, void *);
  uint8_t uu____1[32U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)32U, self->seed_for_A, uu____1, uint8_t, void *);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U][3U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)3U, self->A, ret,
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U], void *);
  memcpy(lit.A, ret,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  return lit;
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2])#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_d2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_clone_d2_d7(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key =
      libcrux_ml_kem_ind_cpa_unpacked_clone_ef_f5(&self->ind_cpa_public_key);
  uint8_t ret[32U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)32U, self->public_key_hash, ret, uint8_t, void *);
  memcpy(lit.public_key_hash, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Get the serialized public key.
*/
/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_fc
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *
libcrux_ml_kem_ind_cca_unpacked_public_key_fc_13(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
 Get the unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_public_key(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *pk) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 uu____0 =
      libcrux_ml_kem_ind_cca_unpacked_clone_d2_d7(
          libcrux_ml_kem_ind_cca_unpacked_public_key_fc_13(key_pair));
  pk[0U] = uu____0;
}

/**
 Read the public key from `bytes``.

 `bytes` has to point to at least 6208 bytes.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_mlkem768_avx2_unpacked_public_key_from_bytes(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_ind_cca_unpacked_from_bytes_dd_96(bytes);
}

/**
 Write out the public key.

 `out` has to point to at least 6208 bytes.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_public_key_to_bytes(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *key,
    Eurydice_slice out) {
  libcrux_ml_kem_ind_cca_unpacked_to_bytes_dd_75(key, out);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    libcrux_ml_kem_types_MlKemPublicKey_15 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_ba_74(public_key,
                                                                  serialized);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash,
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_22(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key->value, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_6d(
      uu____0, unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_423(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2(*uu____2)[3U] =
      unpacked_public_key->ind_cpa_public_key.A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_421(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t),
      ret);
  libcrux_ml_kem_matrix_sample_matrix_A_8e(uu____2, ret, false);
  uint8_t uu____3[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_16(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_ba_c1(public_key),
                              uint8_t),
      uu____3);
  memcpy(unpacked_public_key->public_key_hash, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.unpack_public_key with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_2e(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_22(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_unpacked_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_2e(
      public_key, unpacked_public_key);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#1}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_kem_vector_avx2_clone_3a(__m256i *self) {
  return self[0U];
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_avx2_H_DEFINED
#endif
