/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0576bfc67e99aae86c51930421072688138b672b
 * Eurydice: e66abbc2119485abfafa17c1911bdbdada5b04f3
 * Karamel: 7862fdc3899b718d39ec98568f78ec40592a622a
 * F*: 04413e808445c4f78fe89cd15b85ff549ed3be62
 * Libcrux: 293f3b52093c13f3043781d878990c5be6fc4e23
 */

#ifndef __libcrux_mlkem768_avx2_H
#define __libcrux_mlkem768_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_ct_ops.h"
#include "libcrux_mlkem768_portable.h"
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

typedef core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_SIMD256Vector;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_vec_zero(void) {
  return libcrux_intrinsics_avx2_mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ZERO_09(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array) {
  return libcrux_intrinsics_avx2_mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_from_i16_array_09(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_vec_from_i16_array(array);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_vec_to_i16_array(
    core_core_arch_x86___m256i v, int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, output, int16_t), v);
  int16_t result[16U];
  memcpy(result, output, (size_t)16U * sizeof(int16_t));
  memcpy(ret, result, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_to_i16_array_09(
    core_core_arch_x86___m256i x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_vec_to_i16_array(x, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_add(core_core_arch_x86___m256i lhs,
                                          core_core_arch_x86___m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_add_09(
    core_core_arch_x86___m256i lhs, core_core_arch_x86___m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_sub(core_core_arch_x86___m256i lhs,
                                          core_core_arch_x86___m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_sub_09(
    core_core_arch_x86___m256i lhs, core_core_arch_x86___m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_mullo_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_multiply_by_constant_09(core_core_arch_x86___m256i v,
                                                   int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(v, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_and_si256(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vector, constant);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i v_minus_field_modulus =
      libcrux_intrinsics_avx2_mm256_sub_epi16(vector, field_modulus);
  core_core_arch_x86___m256i sign_mask =
      libcrux_intrinsics_avx2_mm256_srai_epi16(
          (int32_t)15, v_minus_field_modulus, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i conditional_add_field_modulus =
      libcrux_intrinsics_avx2_mm256_and_si256(sign_mask, field_modulus);
  return libcrux_intrinsics_avx2_mm256_add_epi16(v_minus_field_modulus,
                                                 conditional_add_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_cond_subtract_3329_09(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i t = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(
                  LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  core_core_arch_x86___m256i t0 = libcrux_intrinsics_avx2_mm256_add_epi16(
      t, libcrux_intrinsics_avx2_mm256_set1_epi16((int16_t)512));
  core_core_arch_x86___m256i quotient =
      libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)10, t0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i quotient_times_field_modulus =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(
          quotient, libcrux_intrinsics_avx2_mm256_set1_epi16(
                        LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return libcrux_intrinsics_avx2_mm256_sub_epi16(vector,
                                                 quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_barrett_reduce_09(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    core_core_arch_x86___m256i vector, int16_t constant) {
  core_core_arch_x86___m256i constant0 =
      libcrux_intrinsics_avx2_mm256_set1_epi16(constant);
  core_core_arch_x86___m256i value_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(vector, constant0);
  core_core_arch_x86___m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  core_core_arch_x86___m256i k_times_modulus =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(
          k, libcrux_intrinsics_avx2_mm256_set1_epi16(
                 LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  core_core_arch_x86___m256i value_high =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(vector, constant0);
  return libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus_halved =
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) /
          (int16_t)2);
  core_core_arch_x86___m256i field_modulus_quartered =
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) /
          (int16_t)4);
  core_core_arch_x86___m256i shifted =
      libcrux_intrinsics_avx2_mm256_sub_epi16(field_modulus_halved, vector);
  core_core_arch_x86___m256i mask = libcrux_intrinsics_avx2_mm256_srai_epi16(
      (int32_t)15, shifted, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i shifted_to_positive =
      libcrux_intrinsics_avx2_mm256_xor_si256(mask, shifted);
  core_core_arch_x86___m256i shifted_to_positive_in_range =
      libcrux_intrinsics_avx2_mm256_sub_epi16(shifted_to_positive,
                                              field_modulus_quartered);
  return libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)15, shifted_to_positive_in_range, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_1_09(core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(
    core_core_arch_x86___m256i lhs, core_core_arch_x86___m256i rhs) {
  core_core_arch_x86___m256i prod02 =
      libcrux_intrinsics_avx2_mm256_mul_epu32(lhs, rhs);
  core_core_arch_x86___m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epu32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, lhs,
                                                  core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, rhs,
                                                  core_core_arch_x86___m256i));
  return libcrux_intrinsics_avx2_mm256_unpackhi_epi64(
      libcrux_intrinsics_avx2_mm256_unpacklo_epi32(prod02, prod13),
      libcrux_intrinsics_avx2_mm256_unpackhi_epi32(prod02, prod13));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    core_core_arch_x86___m256i v, core_core_arch_x86___m256i c) {
  core_core_arch_x86___m256i value_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(v, c);
  core_core_arch_x86___m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  core_core_arch_x86___m256i k_times_modulus =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(
          k, libcrux_intrinsics_avx2_mm256_set1_epi16(
                 LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  core_core_arch_x86___m256i value_high =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  core_core_arch_x86___m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1,
      -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
  core_core_arch_x86___m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)245, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  core_core_arch_x86___m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)160, vector, core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_layer_1_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  core_core_arch_x86___m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0,
      -zeta0, -zeta0, -zeta0, zeta0, zeta0, zeta0, zeta0);
  core_core_arch_x86___m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)238, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  core_core_arch_x86___m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)68, vector, core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_layer_2_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    core_core_arch_x86___m128i v, core_core_arch_x86___m128i c) {
  core_core_arch_x86___m128i value_low =
      libcrux_intrinsics_avx2_mm_mullo_epi16(v, c);
  core_core_arch_x86___m128i k = libcrux_intrinsics_avx2_mm_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  core_core_arch_x86___m128i k_times_modulus =
      libcrux_intrinsics_avx2_mm_mulhi_epi16(
          k, libcrux_intrinsics_avx2_mm_set1_epi16(
                 LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  core_core_arch_x86___m128i value_high =
      libcrux_intrinsics_avx2_mm_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_mm_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  core_core_arch_x86___m128i rhs =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m128i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          rhs, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  core_core_arch_x86___m128i lhs =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs0);
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs0);
  core_core_arch_x86___m256i combined =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  return libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_layer_3_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  core_core_arch_x86___m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)245, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)160, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1,
               (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1));
  core_core_arch_x86___m256i sum0 =
      libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  core_core_arch_x86___m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum0, libcrux_intrinsics_avx2_mm256_set_epi16(
                    zeta3, zeta3, (int16_t)0, (int16_t)0, zeta2, zeta2,
                    (int16_t)0, (int16_t)0, zeta1, zeta1, (int16_t)0,
                    (int16_t)0, zeta0, zeta0, (int16_t)0, (int16_t)0));
  core_core_arch_x86___m256i sum =
      libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(sum0);
  return libcrux_intrinsics_avx2_mm256_blend_epi16(
      (int32_t)204, sum, sum_times_zetas, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  core_core_arch_x86___m256i lhs =
      libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
          (int32_t)245, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs =
      libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
          (int32_t)160, vector, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)1,
               (int16_t)1));
  core_core_arch_x86___m256i sum =
      libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  core_core_arch_x86___m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum, libcrux_intrinsics_avx2_mm256_set_epi16(
                   zeta1, zeta1, zeta1, zeta1, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, zeta0, zeta0, zeta0, zeta0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0));
  return libcrux_intrinsics_avx2_mm256_blend_epi16(
      (int32_t)240, sum, sum_times_zetas, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  core_core_arch_x86___m128i lhs =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m128i rhs =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs);
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs);
  core_core_arch_x86___m128i upper_coefficients0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          upper_coefficients, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  core_core_arch_x86___m256i combined =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  return libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients0, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_09(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
    core_core_arch_x86___m256i v) {
  core_core_arch_x86___m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      v,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  core_core_arch_x86___m256i k_times_modulus =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(
          k, libcrux_intrinsics_avx2_mm256_set1_epi32(
                 (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  core_core_arch_x86___m256i value_high =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)16, v,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i result =
      libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
  core_core_arch_x86___m256i result0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)16, result, core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)16, result0,
                                                  core_core_arch_x86___m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(core_core_arch_x86___m256i lhs,
                                            core_core_arch_x86___m256i rhs,
                                            int16_t zeta0, int16_t zeta1,
                                            int16_t zeta2, int16_t zeta3) {
  core_core_arch_x86___m256i shuffle_with =
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)15, (int8_t)14, (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6,
          (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8,
          (int8_t)5, (int8_t)4, (int8_t)1, (int8_t)0, (int8_t)15, (int8_t)14,
          (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6, (int8_t)3, (int8_t)2,
          (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
          (int8_t)1, (int8_t)0);
  core_core_arch_x86___m256i lhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(lhs, shuffle_with);
  core_core_arch_x86___m256i lhs_shuffled0 =
      libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
          (int32_t)216, lhs_shuffled, core_core_arch_x86___m256i);
  core_core_arch_x86___m128i lhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(lhs_shuffled0);
  core_core_arch_x86___m256i lhs_evens0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_evens);
  core_core_arch_x86___m128i lhs_odds =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, lhs_shuffled0, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i lhs_odds0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_odds);
  core_core_arch_x86___m256i rhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(rhs, shuffle_with);
  core_core_arch_x86___m256i rhs_shuffled0 =
      libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
          (int32_t)216, rhs_shuffled, core_core_arch_x86___m256i);
  core_core_arch_x86___m128i rhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(rhs_shuffled0);
  core_core_arch_x86___m256i rhs_evens0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_evens);
  core_core_arch_x86___m128i rhs_odds =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, rhs_shuffled0, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i rhs_odds0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_odds);
  core_core_arch_x86___m256i left =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_evens0, rhs_evens0);
  core_core_arch_x86___m256i right =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_odds0, rhs_odds0);
  core_core_arch_x86___m256i right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(right);
  core_core_arch_x86___m256i right1 = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      right0,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          -(int32_t)zeta3, (int32_t)zeta3, -(int32_t)zeta2, (int32_t)zeta2,
          -(int32_t)zeta1, (int32_t)zeta1, -(int32_t)zeta0, (int32_t)zeta0));
  core_core_arch_x86___m256i products_left =
      libcrux_intrinsics_avx2_mm256_add_epi32(left, right1);
  core_core_arch_x86___m256i products_left0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_left);
  core_core_arch_x86___m256i rhs_adjacent_swapped =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          rhs, libcrux_intrinsics_avx2_mm256_set_epi8(
                   (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14, (int8_t)9,
                   (int8_t)8, (int8_t)11, (int8_t)10, (int8_t)5, (int8_t)4,
                   (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0, (int8_t)3,
                   (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14,
                   (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10, (int8_t)5,
                   (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0,
                   (int8_t)3, (int8_t)2));
  core_core_arch_x86___m256i products_right =
      libcrux_intrinsics_avx2_mm256_madd_epi16(lhs, rhs_adjacent_swapped);
  core_core_arch_x86___m256i products_right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_right);
  core_core_arch_x86___m256i products_right1 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)16, products_right0,
                                               core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_blend_epi16((int32_t)170, products_left0,
                                                   products_right1,
                                                   core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_ntt_multiply_09(core_core_arch_x86___m256i *lhs,
                                           core_core_arch_x86___m256i *rhs,
                                           int16_t zeta0, int16_t zeta1,
                                           int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    core_core_arch_x86___m256i vector, uint8_t ret[2U]) {
  core_core_arch_x86___m256i lsb_to_msb =
      libcrux_intrinsics_avx2_mm256_slli_epi16((int32_t)15, vector,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m128i low_msbs =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(lsb_to_msb);
  core_core_arch_x86___m128i high_msbs =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, lsb_to_msb, core_core_arch_x86___m128i);
  core_core_arch_x86___m128i msbs =
      libcrux_intrinsics_avx2_mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = libcrux_intrinsics_avx2_mm_movemask_epi8(msbs);
  uint8_t serialized[2U] = {0U};
  serialized[0U] = (uint8_t)bits_packed;
  serialized[1U] = (uint8_t)(bits_packed >> 8U);
  memcpy(ret, serialized, (size_t)2U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_1_09(
    core_core_arch_x86___m256i vector, uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_set_epi16(
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
  core_core_arch_x86___m256i shift_lsb_to_msb =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U,
          (int16_t)1 << 11U, (int16_t)1 << 12U, (int16_t)1 << 13U,
          (int16_t)1 << 14U, (int16_t)-32768, (int16_t)1 << 8U,
          (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
          (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U,
          (int16_t)-32768);
  core_core_arch_x86___m256i coefficients_in_msb =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
  return libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)15, coefficients_in_msb, core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_1_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    core_core_arch_x86___m256i vector, uint8_t ret[8U]) {
  uint8_t serialized[16U] = {0U};
  core_core_arch_x86___m256i adjacent_2_combined =
      libcrux_intrinsics_avx2_mm256_madd_epi16(
          vector,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1));
  core_core_arch_x86___m256i adjacent_8_combined =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          adjacent_2_combined,
          libcrux_intrinsics_avx2_mm256_set_epi8(
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4,
              (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8,
              (int8_t)4, (int8_t)0));
  core_core_arch_x86___m256i combined =
      libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
          adjacent_8_combined,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
              (int32_t)0, (int32_t)4, (int32_t)0));
  core_core_arch_x86___m128i combined0 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t), combined0);
  uint8_t ret0[8U];
  core_result_Result_56 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)8U, uint8_t),
      Eurydice_slice, uint8_t[8U]);
  core_result_unwrap_41_ac(dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_4_09(
    core_core_arch_x86___m256i vector, uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_set_epi16(
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
  core_core_arch_x86___m256i shift_lsbs_to_msbs =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U);
  core_core_arch_x86___m256i coefficients_in_msb =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(coefficients,
                                                shift_lsbs_to_msbs);
  core_core_arch_x86___m256i coefficients_in_lsb =
      libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)4, coefficients_in_msb,
                                               core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients_in_lsb, libcrux_intrinsics_avx2_mm256_set1_epi16(
                               ((int16_t)1 << 4U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_4_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    core_core_arch_x86___m256i vector, uint8_t ret[10U]) {
  uint8_t serialized[32U] = {0U};
  core_core_arch_x86___m256i adjacent_2_combined =
      libcrux_intrinsics_avx2_mm256_madd_epi16(
          vector,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1));
  core_core_arch_x86___m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_sllv_epi32(
          adjacent_2_combined,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22, (int32_t)0,
              (int32_t)22, (int32_t)0, (int32_t)22));
  core_core_arch_x86___m256i adjacent_4_combined0 =
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)22, adjacent_4_combined,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i adjacent_8_combined =
      libcrux_intrinsics_avx2_mm256_shuffle_epi32(
          (int32_t)8, adjacent_4_combined0, core_core_arch_x86___m256i);
  core_core_arch_x86___m256i adjacent_8_combined0 =
      libcrux_intrinsics_avx2_mm256_sllv_epi32(
          adjacent_8_combined,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12, (int32_t)0,
              (int32_t)0, (int32_t)0, (int32_t)12));
  core_core_arch_x86___m256i adjacent_8_combined1 =
      libcrux_intrinsics_avx2_mm256_srli_epi64(
          (int32_t)12, adjacent_8_combined0, core_core_arch_x86___m256i);
  core_core_arch_x86___m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined1);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  core_core_arch_x86___m128i upper_8 =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_8_combined1, core_core_arch_x86___m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)5U, (size_t)21U, uint8_t),
      upper_8);
  uint8_t ret0[10U];
  core_result_Result_cd dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t),
      Eurydice_slice, uint8_t[10U]);
  core_result_unwrap_41_e8(dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_5_09(
    core_core_arch_x86___m256i vector, uint8_t ret[10U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes) {
  core_core_arch_x86___m128i coefficients = libcrux_intrinsics_avx2_mm_set_epi8(
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
  core_core_arch_x86___m256i coefficients_loaded =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(coefficients);
  core_core_arch_x86___m256i coefficients_loaded0 =
      libcrux_intrinsics_avx2_mm256_inserti128_si256(
          (int32_t)1, coefficients_loaded, coefficients,
          core_core_arch_x86___m256i);
  core_core_arch_x86___m256i coefficients0 =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          coefficients_loaded0,
          libcrux_intrinsics_avx2_mm256_set_epi8(
              (int8_t)15, (int8_t)14, (int8_t)15, (int8_t)14, (int8_t)13,
              (int8_t)12, (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10,
              (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)9,
              (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)7, (int8_t)6, (int8_t)5,
              (int8_t)4, (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)3,
              (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)1, (int8_t)0));
  core_core_arch_x86___m256i coefficients1 =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(
          coefficients0,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1 << 0U, (int16_t)1 << 5U, (int16_t)1 << 2U,
              (int16_t)1 << 7U, (int16_t)1 << 4U, (int16_t)1 << 9U,
              (int16_t)1 << 6U, (int16_t)1 << 11U, (int16_t)1 << 0U,
              (int16_t)1 << 5U, (int16_t)1 << 2U, (int16_t)1 << 7U,
              (int16_t)1 << 4U, (int16_t)1 << 9U, (int16_t)1 << 6U,
              (int16_t)1 << 11U));
  return libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)11, coefficients1,
                                                  core_core_arch_x86___m256i);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_5_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    core_core_arch_x86___m256i vector, uint8_t ret[20U]) {
  uint8_t serialized[32U] = {0U};
  core_core_arch_x86___m256i adjacent_2_combined =
      libcrux_intrinsics_avx2_mm256_madd_epi16(
          vector,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1));
  core_core_arch_x86___m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_sllv_epi32(
          adjacent_2_combined,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12, (int32_t)0,
              (int32_t)12, (int32_t)0, (int32_t)12));
  core_core_arch_x86___m256i adjacent_4_combined0 =
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)12, adjacent_4_combined,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i adjacent_8_combined =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          adjacent_4_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi8(
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9,
              (int8_t)8, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9,
              (int8_t)8, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1,
              (int8_t)0));
  core_core_arch_x86___m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  core_core_arch_x86___m128i upper_8 =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_8_combined, core_core_arch_x86___m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)10U, (size_t)26U,
                                  uint8_t),
      upper_8);
  uint8_t ret0[20U];
  core_result_Result_7a dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t),
      Eurydice_slice, uint8_t[20U]);
  core_result_unwrap_41_34(dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_10_09(
    core_core_arch_x86___m256i vector, uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes) {
  core_core_arch_x86___m256i shift_lsbs_to_msbs =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
          (int16_t)1 << 6U, (int16_t)1 << 0U, (int16_t)1 << 2U,
          (int16_t)1 << 4U, (int16_t)1 << 6U, (int16_t)1 << 0U,
          (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
          (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
          (int16_t)1 << 6U);
  core_core_arch_x86___m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  core_core_arch_x86___m128i lower_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          lower_coefficients,
          libcrux_intrinsics_avx2_mm_set_epi8(9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U,
                                              4U, 3U, 3U, 2U, 2U, 1U, 1U, 0U));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_slice_subslice2(bytes, (size_t)4U, (size_t)20U, uint8_t));
  core_core_arch_x86___m128i upper_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          upper_coefficients, libcrux_intrinsics_avx2_mm_set_epi8(
                                  15U, 14U, 14U, 13U, 13U, 12U, 12U, 11U, 10U,
                                  9U, 9U, 8U, 8U, 7U, 7U, 6U));
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients0);
  core_core_arch_x86___m256i coefficients0 =
      libcrux_intrinsics_avx2_mm256_inserti128_si256(
          (int32_t)1, coefficients, upper_coefficients0,
          core_core_arch_x86___m256i);
  core_core_arch_x86___m256i coefficients1 =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(coefficients0,
                                                shift_lsbs_to_msbs);
  core_core_arch_x86___m256i coefficients2 =
      libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)6, coefficients1,
                                               core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients2, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 10U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_10_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    core_core_arch_x86___m256i vector, uint8_t ret[22U]) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_11_09(
    core_core_arch_x86___m256i vector, uint8_t ret[22U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_11_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    core_core_arch_x86___m256i vector, uint8_t ret[24U]) {
  uint8_t serialized[32U] = {0U};
  core_core_arch_x86___m256i adjacent_2_combined =
      libcrux_intrinsics_avx2_mm256_madd_epi16(
          vector,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1));
  core_core_arch_x86___m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_sllv_epi32(
          adjacent_2_combined,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8, (int32_t)0,
              (int32_t)8, (int32_t)0, (int32_t)8));
  core_core_arch_x86___m256i adjacent_4_combined0 =
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)8, adjacent_4_combined,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i adjacent_8_combined =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          adjacent_4_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi8(
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13,
              (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
              (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13,
              (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
              (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1,
              (int8_t)0));
  core_core_arch_x86___m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  core_core_arch_x86___m128i upper_8 =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_8_combined, core_core_arch_x86___m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_8);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)12U, (size_t)28U,
                                  uint8_t),
      upper_8);
  uint8_t ret0[24U];
  core_result_Result_6f dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)24U, uint8_t),
      Eurydice_slice, uint8_t[24U]);
  core_result_unwrap_41_1c(dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_vector_avx2_serialize_12_09(
    core_core_arch_x86___m256i vector, uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes) {
  core_core_arch_x86___m256i shift_lsbs_to_msbs =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
          (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
          (int16_t)1 << 4U);
  core_core_arch_x86___m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)16U, uint8_t));
  core_core_arch_x86___m128i lower_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          lower_coefficients,
          libcrux_intrinsics_avx2_mm_set_epi8(11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U,
                                              5U, 4U, 4U, 3U, 2U, 1U, 1U, 0U));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_slice_subslice2(bytes, (size_t)8U, (size_t)24U, uint8_t));
  core_core_arch_x86___m128i upper_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          upper_coefficients, libcrux_intrinsics_avx2_mm_set_epi8(
                                  15U, 14U, 14U, 13U, 12U, 11U, 11U, 10U, 9U,
                                  8U, 8U, 7U, 6U, 5U, 5U, 4U));
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients0);
  core_core_arch_x86___m256i coefficients0 =
      libcrux_intrinsics_avx2_mm256_inserti128_si256(
          (int32_t)1, coefficients, upper_coefficients0,
          core_core_arch_x86___m256i);
  core_core_arch_x86___m256i coefficients1 =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(coefficients0,
                                                shift_lsbs_to_msbs);
  core_core_arch_x86___m256i coefficients2 =
      libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)4, coefficients1,
                                               core_core_arch_x86___m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients2, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 12U) - (int16_t)1));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_deserialize_12_09(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_avx2_sampling_rejection_sample(Eurydice_slice input,
                                                     Eurydice_slice output) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i potential_coefficients =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_12(input);
  core_core_arch_x86___m256i compare_with_field_modulus =
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
  core_core_arch_x86___m128i lower_shuffles0 =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  core_core_arch_x86___m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(potential_coefficients);
  core_core_arch_x86___m128i lower_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(lower_coefficients,
                                              lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8_6__count_ones(good[0U]);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[1U]],
         (size_t)16U * sizeof(uint8_t));
  core_core_arch_x86___m128i upper_shuffles0 =
      libcrux_intrinsics_avx2_mm_loadu_si128(
          Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, potential_coefficients, core_core_arch_x86___m128i);
  core_core_arch_x86___m128i upper_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(upper_coefficients,
                                              upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)8U, int16_t),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8_6__count_ones(good[1U]);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline size_t libcrux_ml_kem_vector_avx2_rej_sample_09(
    Eurydice_slice input, Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_d2_s {
  core_core_arch_x86___m256i coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_d2;

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_ZERO_20_d5(void) {
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_deserialize_secret_key_closure_5d(size_t _) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_20(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_deserialize_secret_key_a1(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    secret_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
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
        libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_20(
            secret_bytes);
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
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0;

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
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_closure_c5(size_t _) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_92(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1
                                               << (uint32_t)(int32_t)10);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i decompressed_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_low0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_low0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_low,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_low0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)10, decompressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_low2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i decompressed_high =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_high0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_high0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_high,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_high0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)10, decompressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_high2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(decompressed_low3,
                                                decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f2(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_92(
      vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_10_8a(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  LowStar_Ignore_ignore(
      Eurydice_slice_len(Eurydice_array_to_slice((size_t)16U, re.coefficients,
                                                 core_core_arch_x86___m256i),
                         core_core_arch_x86___m256i),
      size_t, void *);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_10_09(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f2(
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_920(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1
                                               << (uint32_t)(int32_t)11);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i decompressed_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_low0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_low0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_low,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_low0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)11, decompressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_low2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i decompressed_high =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_high0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_high0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_high,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_high0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)11, decompressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_high2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(decompressed_low3,
                                                decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f20(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_920(
      vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_11_4e(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_11_09(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f20(
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
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_7d(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_10_8a(serialized);
}

typedef struct libcrux_ml_kem_vector_avx2_SIMD256Vector_x2_s {
  core_core_arch_x86___m256i fst;
  core_core_arch_x86___m256i snd;
} libcrux_ml_kem_vector_avx2_SIMD256Vector_x2;

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_traits_montgomery_multiply_fe_55(
    core_core_arch_x86___m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
libcrux_ml_kem_ntt_ntt_layer_int_vec_step_88(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b,
                                             int16_t zeta_r) {
  core_core_arch_x86___m256i t =
      libcrux_ml_kem_vector_traits_montgomery_multiply_fe_55(b, zeta_r);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(
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
          libcrux_ml_kem_ntt_ntt_layer_int_vec_step_88(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      core_core_arch_x86___m256i x = uu____0.fst;
      core_core_arch_x86___m256i y = uu____0.snd;
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
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_3_45(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_09(
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
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_2_10(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_09(
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
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_1_83(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer, size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_1_step_09(
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_20_94(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    self->coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_09(self->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_vector_u_05(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)7U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)6U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)5U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)4U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_45(&zeta_i, re, (size_t)3U, (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_10(&zeta_i, re, (size_t)2U, (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_83(&zeta_i, re, (size_t)1U, (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_20_94(re);
}

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
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_54(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    u_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
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
        libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_7d(
            u_bytes);
    libcrux_ml_kem_ntt_ntt_vector_u_05(&u_as_ntt[i0]);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_921(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1
                                               << (uint32_t)(int32_t)4);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i decompressed_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_low0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_low0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_low,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_low0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)4, decompressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_low2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i decompressed_high =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_high0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_high0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_high,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_high0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)4, decompressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_high2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(decompressed_low3,
                                                decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f21(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_921(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_4_c1(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_4_09(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f21(
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_922(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  core_core_arch_x86___m256i two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1
                                               << (uint32_t)(int32_t)5);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i decompressed_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_low0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_low0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_low,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_low0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)5, decompressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_low3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_low2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i decompressed_high =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(coefficients_high0,
                                                field_modulus);
  core_core_arch_x86___m256i decompressed_high0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)1, decompressed_high,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high1 =
      libcrux_intrinsics_avx2_mm256_add_epi32(decompressed_high0,
                                              two_pow_coefficient_bits);
  core_core_arch_x86___m256i decompressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)5, decompressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i decompressed_high3 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)1, decompressed_high2,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(decompressed_low3,
                                                decompressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f22(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_922(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_then_decompress_5_8e(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_09(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_09_f22(
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
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_96(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_4_c1(serialized);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_ntt_multiply_20_41(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    out.coefficients[i0] = libcrux_ml_kem_vector_avx2_ntt_multiply_09(
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
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_20_87(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, self->coefficients,
                                       core_core_arch_x86___m256i),
               core_core_arch_x86___m256i);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_09(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_29(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_09(
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
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_9c(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_09(
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
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_bc(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re,
    size_t _layer) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_09(
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
libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_8c(
    core_core_arch_x86___m256i a, core_core_arch_x86___m256i b,
    int16_t zeta_r) {
  core_core_arch_x86___m256i a_minus_b =
      libcrux_ml_kem_vector_avx2_sub_09(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_09(
      libcrux_ml_kem_vector_avx2_add_09(a, &b));
  b = libcrux_ml_kem_vector_traits_montgomery_multiply_fe_55(a_minus_b, zeta_r);
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
libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_e6(
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
          libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_8c(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      core_core_arch_x86___m256i x = uu____0.fst;
      core_core_arch_x86___m256i y = uu____0.snd;
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
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_40(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_29(&zeta_i, re, (size_t)1U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_9c(&zeta_i, re, (size_t)2U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_bc(&zeta_i, re, (size_t)3U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_e6(&zeta_i, re,
                                                          (size_t)4U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_e6(&zeta_i, re,
                                                          (size_t)5U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_e6(&zeta_i, re,
                                                          (size_t)6U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_e6(&zeta_i, re,
                                                          (size_t)7U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_20_94(re);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_subtract_reduce_20_ee(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient_normal_form =
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_message_2c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
        libcrux_ml_kem_polynomial_ntt_multiply_20_41(&secret_as_ntt[i0],
                                                     &u_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_20_87(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_40(&result);
  result = libcrux_ml_kem_polynomial_subtract_reduce_20_ee(v, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_shift_right_81(
    core_core_arch_x86___m256i vector) {
  return libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, vector,
                                                  core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_shift_right_09_da(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_shift_right_81(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
    core_core_arch_x86___m256i a) {
  core_core_arch_x86___m256i t =
      libcrux_ml_kem_vector_avx2_shift_right_09_da(a);
  core_core_arch_x86___m256i fm =
      libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_09(a, &fm);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_message_b8(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
            re.coefficients[i0]);
    core_core_arch_x86___m256i coefficient_compressed =
        libcrux_ml_kem_vector_avx2_compress_1_09(coefficient);
    uint8_t bytes[2U];
    libcrux_ml_kem_vector_avx2_serialize_1_09(coefficient_compressed, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)2U * i0, (size_t)2U * i0 + (size_t)2U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)2U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)32U * sizeof(uint8_t));
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_decrypt_unpacked_28(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_54(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_96(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      libcrux_ml_kem_matrix_compute_message_2c(&v, secret_key->secret_as_ntt,
                                               u_as_ntt);
  uint8_t ret0[32U];
  libcrux_ml_kem_serialize_compress_then_serialize_message_b8(message, ret0);
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
static inline void libcrux_ml_kem_ind_cpa_decrypt_20(Eurydice_slice secret_key,
                                                     uint8_t *ciphertext,
                                                     uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  libcrux_ml_kem_ind_cpa_deserialize_secret_key_a1(secret_key, secret_as_ntt);
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
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_28(&secret_key_unpacked, ciphertext,
                                             result);
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G_a9_68(
    Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_42(
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
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_a9_93(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_PRF_42(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_closure_87(
    size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_3b(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_12_09(bytes);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_e7(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    deserialized_pk[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
  }
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
        libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_3b(
            ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_sample_matrix_A_closure_closure_a6(size_t _j) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_matrix_sample_matrix_A_closure_b8(
    size_t _i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
  }
}

typedef libcrux_sha3_avx2_x4_incremental_KeccakState
    libcrux_ml_kem_hash_functions_avx2_Simd256Hash;

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_4d(
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
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_a9 with const
generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_a9_ca(
    uint8_t input[3U][34U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_input[3U][34U];
  memcpy(copy_of_input, input, (size_t)3U * sizeof(uint8_t[34U]));
  return libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_4d(
      copy_of_input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_6b(
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_a9_4d(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_6b(
      self, ret);
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
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_bb(
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
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block with const
generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_1b(
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_a9_5a(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_1b(self, ret);
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
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_bb0(
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
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_09(
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_from_i16_array_20_10(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_xof_closure_79(int16_t s[272U]) {
  return libcrux_ml_kem_polynomial_from_i16_array_20_10(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_b0(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seeds[3U][34U];
  memcpy(copy_of_seeds, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_a9_ca(
          copy_of_seeds);
  uint8_t randomness0[3U][504U];
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_a9_4d(
      &xof_state, randomness0);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness0[3U][504U];
  memcpy(copy_of_randomness0, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_bb(
      copy_of_randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_a9_5a(
          &xof_state, randomness);
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_randomness[3U][168U];
      memcpy(copy_of_randomness, randomness,
             (size_t)3U * sizeof(uint8_t[168U]));
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_bb0(
          copy_of_randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret0[i] =
        libcrux_ml_kem_sampling_sample_from_xof_closure_79(copy_of_out[i]);
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
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_a2(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[3U][3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    libcrux_ml_kem_matrix_sample_matrix_A_closure_b8(i, A_transpose[i]);
  }
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
    libcrux_ml_kem_sampling_sample_from_xof_b0(copy_of_seeds, sampled);
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
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U][3U];
  memcpy(result, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(ret, result,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0;

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
libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt.closure with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_closure_84(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN_1c(
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
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_51(
    uint8_t (*input)[33U], uint8_t ret[3U][128U]) {
  libcrux_ml_kem_hash_functions_avx2_PRFxN_1c(input, ret);
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
libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_25(
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
  return libcrux_ml_kem_polynomial_from_i16_array_20_10(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_sampling_sample_from_binomial_distribution_3_92(
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
  return libcrux_ml_kem_polynomial_from_i16_array_20_10(
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
libcrux_ml_kem_sampling_sample_from_binomial_distribution_92(
    Eurydice_slice randomness) {
  return libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_25(
      randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_7_64(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    core_core_arch_x86___m256i t =
        libcrux_ml_kem_vector_avx2_multiply_by_constant_09(
            re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_avx2_sub_09(re->coefficients[j], &t);
    re->coefficients[j] =
        libcrux_ml_kem_vector_avx2_add_09(re->coefficients[j], &t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_48(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  libcrux_ml_kem_ntt_ntt_at_layer_7_64(re);
  size_t zeta_i = (size_t)1U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)6U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)5U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_b8(&zeta_i, re, (size_t)4U,
                                            (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_45(&zeta_i, re, (size_t)3U, (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_10(&zeta_i, re, (size_t)2U, (size_t)3U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_83(&zeta_i, re, (size_t)1U, (size_t)3U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_20_94(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE tuple_b00
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_70(uint8_t prf_input[33U],
                                                     uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    re_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
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
  libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_51(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    re_as_ntt[i0] =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_92(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_48(&re_as_ntt[i0]);
  }
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_re_as_ntt[3U];
  memcpy(
      copy_of_re_as_ntt, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 result;
  memcpy(
      result.fst, copy_of_re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  result.snd = domain_separator;
  return result;
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
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_closure_4b(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

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
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_4f(uint8_t prf_input[33U],
                                                  uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    error_1[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
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
  libcrux_ml_kem_hash_functions_avx2_PRFxN_a9_51(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_92(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    error_1[i0] = uu____1;
  }
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 copy_of_error_1[3U];
  memcpy(
      copy_of_error_1, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 result;
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_420(
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
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_a9_930(
    Eurydice_slice input, uint8_t ret[128U]) {
  libcrux_ml_kem_hash_functions_avx2_PRF_420(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_vector_u_closure_7d(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_20_b1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    core_core_arch_x86___m256i coefficient_normal_form =
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_vector_u_4f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    result0[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
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
          libcrux_ml_kem_polynomial_ntt_multiply_20_41(a_element, &r_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_20_87(&result0[i1],
                                                          &product);
    }
    libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_40(&result0[i1]);
    libcrux_ml_kem_polynomial_add_error_reduce_20_b1(&result0[i1],
                                                     &error_1[i1]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_traits_decompress_1_14(core_core_arch_x86___m256i v) {
  return libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_09(
      libcrux_ml_kem_vector_avx2_sub_09(libcrux_ml_kem_vector_avx2_ZERO_09(),
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
libcrux_ml_kem_serialize_deserialize_then_decompress_message_48(
    uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient_compressed =
        libcrux_ml_kem_vector_avx2_deserialize_1_09(
            Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                        (size_t)2U * i0 + (size_t)2U, uint8_t));
    re.coefficients[i0] =
        libcrux_ml_kem_vector_traits_decompress_1_14(coefficient_compressed);
  }
  return re;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_add_message_error_reduce_20_24(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
            result.coefficients[i0], (int16_t)1441);
    core_core_arch_x86___m256i tmp = libcrux_ml_kem_vector_avx2_add_09(
        self->coefficients[i0], &message->coefficients[i0]);
    core_core_arch_x86___m256i tmp0 =
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_ring_element_v_41(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result =
      libcrux_ml_kem_polynomial_ZERO_20_d5();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
        libcrux_ml_kem_polynomial_ntt_multiply_20_41(&t_as_ntt[i0],
                                                     &r_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_20_87(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_40(&result);
  result = libcrux_ml_kem_polynomial_add_message_error_reduce_20_24(
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_88(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus_halved =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  core_core_arch_x86___m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  core_core_arch_x86___m256i coefficient_bits_mask =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)10) - (int32_t)1);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i compressed_low =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)10, coefficients_low0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_low,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_low2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i compressed_high =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)10, coefficients_high0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_high,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_high2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(compressed_low3,
                                                compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_09_9c(core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_88(
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
libcrux_ml_kem_serialize_compress_then_serialize_10_43(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_compress_09_9c(
            libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
                re->coefficients[i0]));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_880(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus_halved =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  core_core_arch_x86___m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  core_core_arch_x86___m256i coefficient_bits_mask =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)11) - (int32_t)1);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i compressed_low =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)11, coefficients_low0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_low,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_low2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i compressed_high =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)11, coefficients_high0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_high,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_high2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(compressed_low3,
                                                compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_09_9c0(core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_880(
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
libcrux_ml_kem_serialize_compress_then_serialize_11_b6(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_compress_09_9c0(
            libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
                re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2_serialize_11_09(coefficient, bytes);
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
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_610(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  libcrux_ml_kem_serialize_compress_then_serialize_10_43(re, uu____0);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_compress_then_serialize_u_3a(
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
    libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_610(&re,
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_881(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus_halved =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  core_core_arch_x86___m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  core_core_arch_x86___m256i coefficient_bits_mask =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)4) - (int32_t)1);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i compressed_low =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)4, coefficients_low0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_low,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_low2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i compressed_high =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)4, coefficients_high0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_high,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_high2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(compressed_low3,
                                                compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_09_9c1(core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_881(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_4_f8(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  LowStar_Ignore_ignore(Eurydice_slice_len(serialized, uint8_t), size_t,
                        void *);
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_compress_09_9c1(
            libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
                re.coefficients[i0]));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_882(
    core_core_arch_x86___m256i vector) {
  core_core_arch_x86___m256i field_modulus_halved =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  core_core_arch_x86___m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  core_core_arch_x86___m256i coefficient_bits_mask =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)5) - (int32_t)1);
  core_core_arch_x86___m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector);
  core_core_arch_x86___m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  core_core_arch_x86___m256i compressed_low =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)5, coefficients_low0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_low,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_low2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_low1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_low3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_low2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m128i coefficients_high =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, vector, core_core_arch_x86___m128i);
  core_core_arch_x86___m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  core_core_arch_x86___m256i compressed_high =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)5, coefficients_high0,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high0 =
      libcrux_intrinsics_avx2_mm256_add_epi32(compressed_high,
                                              field_modulus_halved);
  core_core_arch_x86___m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  core_core_arch_x86___m256i compressed_high2 =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)3, compressed_high1,
                                               core_core_arch_x86___m256i);
  core_core_arch_x86___m256i compressed_high3 =
      libcrux_intrinsics_avx2_mm256_and_si256(compressed_high2,
                                              coefficient_bits_mask);
  core_core_arch_x86___m256i compressed =
      libcrux_intrinsics_avx2_mm256_packs_epi32(compressed_low3,
                                                compressed_high3);
  return libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, core_core_arch_x86___m256i);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_compress_09_9c2(core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_882(
      vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_5_e0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  LowStar_Ignore_ignore(Eurydice_slice_len(serialized, uint8_t), size_t,
                        void *);
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficients =
        libcrux_ml_kem_vector_avx2_compress_09_9c2(
            libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
                re.coefficients[i0]));
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_ba(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  libcrux_ml_kem_serialize_compress_then_serialize_4_f8(re, out);
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_encrypt_unpacked_cb(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(randomness, prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____1 = libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_70(
      copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____3 = libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_4f(
      copy_of_prf_input, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_930(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t), prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      libcrux_ml_kem_sampling_sample_from_binomial_distribution_92(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  libcrux_ml_kem_matrix_compute_vector_u_4f(public_key->A, r_as_ntt, error_1,
                                            u);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_message[32U];
  memcpy(copy_of_message, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      libcrux_ml_kem_serialize_deserialize_then_decompress_message_48(
          copy_of_message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      libcrux_ml_kem_matrix_compute_ring_element_v_41(
          public_key->t_as_ntt, r_as_ntt, &error_2, &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_compress_then_serialize_u_3a(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_ba(
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
static inline void libcrux_ml_kem_ind_cpa_encrypt_dd(Eurydice_slice public_key,
                                                     uint8_t message[32U],
                                                     Eurydice_slice randomness,
                                                     uint8_t ret[1088U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_e7(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t),
      t_as_ntt);
  Eurydice_slice seed =
      Eurydice_slice_subslice_from(public_key, (size_t)1152U, uint8_t, size_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed, ret0);
  libcrux_ml_kem_matrix_sample_matrix_A_a2(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_83(dst, seed_for_A);
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
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_cb(uu____3, copy_of_message,
                                             randomness, result);
  memcpy(ret, result, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_43
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_kdf_43_35(
    Eurydice_slice shared_secret, libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_,
    uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, shared_secret, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_83(dst, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
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
static inline void libcrux_ml_kem_ind_cca_decapsulate_99(
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
  libcrux_ml_kem_ind_cpa_decrypt_20(ind_cpa_secret_key, ciphertext->value,
                                    decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_2d0(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_93(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_dd(uu____5, copy_of_decrypted,
                                    pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_ind_cca_kdf_43_35(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t),
      ciphertext, implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  libcrux_ml_kem_ind_cca_kdf_43_35(shared_secret0, ciphertext, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  uint8_t result[32U];
  memcpy(result, shared_secret, (size_t)32U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
}

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
static inline void libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_8a(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_99(private_key, ciphertext, ret);
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
  libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_8a(private_key,
                                                            ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0;

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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_a8(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_28(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
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
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_2d0(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_93(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_cb(
      uu____3, copy_of_decrypted, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
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
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate_unpacked with const
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
libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_unpacked_a5(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_a8(key_pair, ciphertext,
                                                          ret);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_unpacked_a5(
      private_key, ciphertext, ret);
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.entropy_preprocess_43
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_entropy_preprocess_43_a5(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, randomness, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_83(dst, ret);
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
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H_a9_65(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_encapsulate_6d(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  libcrux_ml_kem_ind_cca_entropy_preprocess_43_a5(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_f6_fe(public_key),
                              uint8_t),
      ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_f6_fe(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_dd(uu____2, copy_of_randomness,
                                    pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_15_58(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  libcrux_ml_kem_ind_cca_kdf_43_35(shared_secret, &ciphertext0,
                                   shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_3c result;
  result.fst = uu____5;
  memcpy(result.snd, copy_of_shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  return result;
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
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c
libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_11(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_6d(uu____0, copy_of_randomness);
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
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_11(
      uu____0, copy_of_randomness);
}

/**
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_e6(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  Eurydice_slice_copy(uu____0,
                      Eurydice_array_to_slice(
                          (size_t)32U, public_key->public_key_hash, uint8_t),
                      uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
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
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_cb(uu____2, copy_of_randomness,
                                             pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types_from_15_58(copy_of_ciphertext);
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
 Portable encapsualte
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate_unpacked with const
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
libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_unpacked_18(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_e6(
      uu____0, copy_of_randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_mlkem768_avx2_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_unpacked_18(
      uu____0, copy_of_randomness);
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$3size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$3size_t]]

*/
typedef struct tuple_9b0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 snd;
} tuple_9b0;

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_matrix_compute_As_plus_e_closure_1f(size_t _i) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i
libcrux_ml_kem_vector_traits_to_standard_domain_f0(
    core_core_arch_x86___m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_09(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_20
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_20_a5(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        libcrux_ml_kem_vector_traits_to_standard_domain_f0(
            self->coefficients[j]);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_As_plus_e_bb(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    result0[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
  }
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
          libcrux_ml_kem_polynomial_ntt_multiply_20_41(matrix_element,
                                                       &s_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_20_87(&result0[i1],
                                                          &product);
    }
    libcrux_ml_kem_polynomial_add_standard_error_reduce_20_a5(
        &result0[i1], &error_as_ntt[i1]);
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_9b0 libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_75(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[3U][3U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed_for_A0, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_a2(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(seed_for_secret_and_error,
                                             prf_input);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input0[33U];
  memcpy(copy_of_prf_input0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____2 = libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_70(
      copy_of_prf_input0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_70(copy_of_prf_input,
                                                           domain_separator)
          .fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  libcrux_ml_kem_matrix_compute_As_plus_e_bb(A_transpose, secret_as_ntt,
                                             error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U]);
  core_result_unwrap_41_83(dst, seed_for_A);
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
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_d7(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_traits_to_unsigned_representative_d4(
            re->coefficients[i0]);
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
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 1152
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_secret_key_a8(
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
    libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_d7(&re, ret0);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret0, uint8_t), uint8_t);
  }
  memcpy(ret, out, (size_t)1152U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_fb(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)1152U, uint8_t);
  uint8_t ret0[1152U];
  libcrux_ml_kem_ind_cpa_serialize_secret_key_a8(t_as_ntt, ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)1152U, ret0, uint8_t), uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key_serialized,
                                      (size_t)1152U, uint8_t, size_t),
      seed_for_a, uint8_t);
  uint8_t result[1184U];
  memcpy(result, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)1184U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_utils_extraction_helper_Keypair768
libcrux_ml_kem_ind_cpa_generate_keypair_4f(Eurydice_slice key_generation_seed) {
  tuple_9b0 uu____0 =
      libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_75(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 pk = uu____0.snd;
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_fb(
      pk.t_as_ntt, Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  libcrux_ml_kem_ind_cpa_serialize_secret_key_a8(sk.secret_as_ntt,
                                                 secret_key_serialized);
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
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_9a(
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
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(public_key, ret0);
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
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_11(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      libcrux_ml_kem_ind_cpa_generate_keypair_4f(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_9a(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_e7_ea(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_64_67(
      uu____2, libcrux_ml_kem_types_from_07_0e(copy_of_public_key));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_75(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_11(copy_of_randomness);
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
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_75(
      copy_of_randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.generate_keypair_unpacked.closure.closure with
types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
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
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_closure_closure_39(
    size_t _j) {
  return libcrux_ml_kem_polynomial_ZERO_20_d5();
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_closure_9b(
    size_t _i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret[i] = libcrux_ml_kem_polynomial_ZERO_20_d5();
  }
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2
libcrux_ml_kem_polynomial_clone_3a_47(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 lit;
  core_core_arch_x86___m256i ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret, core_core_arch_x86___m256i, void *);
  memcpy(lit.coefficients, ret,
         (size_t)16U * sizeof(core_core_arch_x86___m256i));
  return lit;
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_7e(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t);
  tuple_9b0 uu____0 = libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_75(
      ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_closure_9b(i,
                                                                         A[i]);
  }
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          libcrux_ml_kem_polynomial_clone_3a_47(&ind_cpa_public_key.A[j][i1]);
      A[i1][j] = uu____1;
    }
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[3U][3U];
  memcpy(uu____2, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t pk_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_fb(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t),
      pk_serialized);
  uint8_t public_key_hash[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t),
      public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U]);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
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
}

/**
 Unpacked API
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair_unpacked with const
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
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_unpacked_7d(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_7e(
      copy_of_randomness);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_unpacked_7d(
      copy_of_randomness);
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::Kyber)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_6c
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_kdf_6c_e5(
    Eurydice_slice shared_secret,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t kdf_input[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(shared_secret, kdf_input);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, kdf_input, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(
      Eurydice_array_to_slice((size_t)1088U,
                              libcrux_ml_kem_types_as_slice_a8_69(ciphertext),
                              uint8_t),
      ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t ret1[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_93(
      Eurydice_array_to_slice((size_t)64U, kdf_input, uint8_t), ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_Kyber
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
static inline void libcrux_ml_kem_ind_cca_decapsulate_990(
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
  libcrux_ml_kem_ind_cpa_decrypt_20(ind_cpa_secret_key, ciphertext->value,
                                    decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_2d0(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t);
  Eurydice_slice_copy(uu____4, libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  libcrux_ml_kem_hash_functions_avx2_PRF_a9_93(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_decrypted[32U];
  memcpy(copy_of_decrypted, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_dd(uu____5, copy_of_decrypted,
                                    pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_ind_cca_kdf_6c_e5(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t),
      ciphertext, implicit_rejection_shared_secret);
  uint8_t shared_secret1[32U];
  libcrux_ml_kem_ind_cca_kdf_6c_e5(shared_secret0, ciphertext, shared_secret1);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_ba_ef(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret1, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      shared_secret);
  uint8_t result[32U];
  memcpy(result, shared_secret, (size_t)32U * sizeof(uint8_t));
  memcpy(ret, result, (size_t)32U * sizeof(uint8_t));
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
libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_decapsulate_29(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_990(private_key, ciphertext, ret);
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
  libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_decapsulate_29(
      private_key, ciphertext, ret);
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::Kyber)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.entropy_preprocess_6c
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_entropy_preprocess_6c_76(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(randomness, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_Kyber
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
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_3c libcrux_ml_kem_ind_cca_encapsulate_6d0(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  libcrux_ml_kem_ind_cca_entropy_preprocess_6c_76(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t);
  uint8_t ret[32U];
  libcrux_ml_kem_hash_functions_avx2_H_a9_65(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_f6_fe(public_key),
                              uint8_t),
      ret);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_avx2_G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_f6_fe(public_key), uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_dd(uu____2, copy_of_randomness,
                                    pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_15_58(copy_of_ciphertext);
  uint8_t shared_secret_array[32U];
  libcrux_ml_kem_ind_cca_kdf_6c_e5(shared_secret, &ciphertext0,
                                   shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_3c result;
  result.fst = uu____5;
  memcpy(result.snd, copy_of_shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  return result;
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
libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_encapsulate_86(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_6d0(uu____0, copy_of_randomness);
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
  return libcrux_ml_kem_ind_cca_instantiations_avx2_kyber_encapsulate_86(
      uu____0, copy_of_randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_public_key_15(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_e7(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_fb(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_1b(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_15(public_key);
}

/**
 Validate a public key.

 Returns `Some(public_key)` if valid, and `None` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_option_Option_92
libcrux_ml_kem_mlkem768_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_15 public_key) {
  core_option_Option_92 uu____0;
  if (libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_1b(
          public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_92){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_92){.tag = core_option_None});
  }
  return uu____0;
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_clone_78(
    core_core_arch_x86___m256i *self) {
  return self[0U];
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_avx2_H_DEFINED
#endif
