/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: 3ed3c98d39ce028c31c5908a38bc68ad5098f563
 * Libcrux: aa91a6764bde8c1f15107a03746f506e99a9159b
 */

#include "internal/libcrux_mlkem_avx2.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"
#include "internal/libcrux_sha3_avx2.h"

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input,
                                                          uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input,
                                                          uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_zero(void) {
  return libcrux_intrinsics_avx2_mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_ZERO_ea(void) {
  return libcrux_ml_kem_vector_avx2_zero();
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array) {
  return libcrux_intrinsics_avx2_mm256_loadu_si256_i16(array);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_from_i16_array_ea(
    Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_i16_array(
    core_core_arch_x86___m256i v, int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, output, int16_t, Eurydice_slice), v);
  memcpy(ret, output, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_to_i16_array_ea(core_core_arch_x86___m256i x,
                                                int16_t ret[16U]) {
  libcrux_ml_kem_vector_avx2_to_i16_array(x, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_add(core_core_arch_x86___m256i lhs,
                                          core_core_arch_x86___m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_add_ea(
    core_core_arch_x86___m256i lhs, core_core_arch_x86___m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_sub(core_core_arch_x86___m256i lhs,
                                          core_core_arch_x86___m256i rhs) {
  return libcrux_intrinsics_avx2_mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_sub_ea(
    core_core_arch_x86___m256i lhs, core_core_arch_x86___m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_mullo_epi16(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
    core_core_arch_x86___m256i v, int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(v, c);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_intrinsics_avx2_mm256_and_si256(
      vector, libcrux_intrinsics_avx2_mm256_set1_epi16(constant));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vector, constant);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
    core_core_arch_x86___m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_compress_1_ea(
    core_core_arch_x86___m256i vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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

KRML_MUSTINLINE core_core_arch_x86___m256i
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

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_MUSTINLINE core_core_arch_x86___m128i
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

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(
    core_core_arch_x86___m256i vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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

KRML_MUSTINLINE core_core_arch_x86___m256i
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_ntt_multiply_ea(
    core_core_arch_x86___m256i *lhs, core_core_arch_x86___m256i *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_1_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[2U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t));
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_1_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
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
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t, Eurydice_slice),
      combined0);
  uint8_t ret0[8U];
  core_result_Result_56 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)8U, uint8_t,
                                  Eurydice_slice),
      Eurydice_slice, uint8_t[8U], void *);
  core_result_unwrap_41_ac(dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_4_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[8U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  core_core_arch_x86___m256i coefficients =
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t),
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                        uint8_t));
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_4_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
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
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t,
                                  Eurydice_slice),
      lower_8);
  core_core_arch_x86___m128i upper_8 =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_8_combined1, core_core_arch_x86___m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)5U, (size_t)21U, uint8_t,
                                  Eurydice_slice),
      upper_8);
  uint8_t ret0[10U];
  core_result_Result_cd dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t,
                                  Eurydice_slice),
      Eurydice_slice, uint8_t[10U], void *);
  core_result_unwrap_41_e8(dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_5_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[10U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes) {
  core_core_arch_x86___m128i coefficients = libcrux_intrinsics_avx2_mm_set_epi8(
      Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *, uint8_t),
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *, uint8_t));
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_5_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
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
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t,
                                  Eurydice_slice),
      lower_8);
  core_core_arch_x86___m128i upper_8 =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_8_combined, core_core_arch_x86___m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)10U, (size_t)26U, uint8_t,
                                  Eurydice_slice),
      upper_8);
  uint8_t ret0[20U];
  core_result_Result_7a dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t,
                                  Eurydice_slice),
      Eurydice_slice, uint8_t[20U], void *);
  core_result_unwrap_41_34(dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_10_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[20U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_slice_subslice2(
          bytes, (size_t)0U, (size_t)16U, uint8_t, Eurydice_slice));
  core_core_arch_x86___m128i lower_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          lower_coefficients,
          libcrux_intrinsics_avx2_mm_set_epi8(9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U,
                                              4U, 3U, 3U, 2U, 2U, 1U, 1U, 0U));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_slice_subslice2(
          bytes, (size_t)4U, (size_t)20U, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_10_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    core_core_arch_x86___m256i vector, uint8_t ret[22U]) {
  int16_t array[16U] = {0U};
  libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice),
      vector);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable_from_i16_array_0d(
          Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_11_0d(input, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_11_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[22U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_11_0d(bytes);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  return libcrux_intrinsics_avx2_mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_11_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
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
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t,
                                  Eurydice_slice),
      lower_8);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)12U, (size_t)28U, uint8_t,
                                  Eurydice_slice),
      upper_8);
  uint8_t ret0[24U];
  core_result_Result_6f dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)24U, uint8_t,
                                  Eurydice_slice),
      Eurydice_slice, uint8_t[24U], void *);
  core_result_unwrap_41_1c(dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_12_ea(
    core_core_arch_x86___m256i vector, uint8_t ret[24U]) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret);
}

KRML_MUSTINLINE core_core_arch_x86___m256i
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
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_slice_subslice2(
          bytes, (size_t)0U, (size_t)16U, uint8_t, Eurydice_slice));
  core_core_arch_x86___m128i lower_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(
          lower_coefficients,
          libcrux_intrinsics_avx2_mm_set_epi8(11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U,
                                              5U, 4U, 4U, 3U, 2U, 1U, 1U, 0U));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_slice_subslice2(
          bytes, (size_t)8U, (size_t)24U, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_deserialize_12_ea(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output) {
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
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_array_to_slice(
          (size_t)16U, lower_shuffles, uint8_t, Eurydice_slice));
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
      libcrux_intrinsics_avx2_mm_loadu_si128(Eurydice_array_to_slice(
          (size_t)16U, upper_shuffles, uint8_t, Eurydice_slice));
  core_core_arch_x86___m128i upper_coefficients =
      libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, potential_coefficients, core_core_arch_x86___m128i);
  core_core_arch_x86___m128i upper_coefficients0 =
      libcrux_intrinsics_avx2_mm_shuffle_epi8(upper_coefficients,
                                              upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)8U, int16_t,
                               Eurydice_slice),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8_6__count_ones(good[1U]);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
size_t libcrux_ml_kem_vector_avx2_rej_sample_ea(Eurydice_slice input,
                                                Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#1}
*/
inline core_core_arch_x86___m256i libcrux_ml_kem_vector_avx2_clone_3a(
    core_core_arch_x86___m256i *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ZERO_89_d5(void) {
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
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_reduced_ring_element_dd(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t,
        Eurydice_slice);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_12_ea(bytes);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1184
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d4(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
shift_right_98(core_core_arch_x86___m256i vector) {
  return libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, vector,
                                                  core_core_arch_x86___m256i);
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
static core_core_arch_x86___m256i shift_right_ea_92(
    core_core_arch_x86___m256i vector) {
  return shift_right_98(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static core_core_arch_x86___m256i to_unsigned_representative_a4(
    core_core_arch_x86___m256i a) {
  core_core_arch_x86___m256i t = shift_right_ea_92(a);
  core_core_arch_x86___m256i fm =
      libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_add_ea(a, &fm);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_92(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        to_unsigned_representative_a4(re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2_serialize_12_ea(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)24U * i0, (size_t)24U * i0 + (size_t)24U, uint8_t,
        Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)24U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
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
static KRML_MUSTINLINE void serialize_secret_key_ae1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[1152U]) {
  uint8_t out[1152U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_92(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
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
static KRML_MUSTINLINE void serialize_public_key_d01(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(public_key_serialized, (size_t)0U,
                                  (size_t)1152U, uint8_t, Eurydice_slice);
  uint8_t ret0[1152U];
  serialize_secret_key_ae1(t_as_ntt, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)1152U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key_serialized,
                                      (size_t)1152U, uint8_t, size_t,
                                      Eurydice_slice),
      seed_for_a, uint8_t, void *);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_cf1(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  deserialize_ring_elements_reduced_5d4(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_d01(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
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
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 3
*/
static KRML_MUSTINLINE void G_a9_681(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static void closure_b81(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_4d1(uint8_t input[3U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice));
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
shake128_init_absorb_final_a9_ca1(uint8_t input[3U][34U]) {
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_4d1(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_6b1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[3U][504U]) {
  uint8_t out[3U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_4d1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_first_three_blocks_6b1(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb3(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_1b1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[3U][168U]) {
  uint8_t out[3U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_5a1(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_next_block_1b1(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb4(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
from_i16_array_89_10(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice_subslice2(
            a, i0 * (size_t)16U, (i0 + (size_t)1U) * (size_t)16U, int16_t,
            Eurydice_slice));
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_791(
    int16_t s[272U]) {
  return from_i16_array_89_10(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_b01(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_ca1(uu____0);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_first_three_blocks_a9_4d1(&xof_state, randomness0);
  uint8_t uu____1[3U][504U];
  memcpy(uu____1, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_bb3(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      shake128_squeeze_next_block_a9_5a1(&xof_state, randomness);
      uint8_t uu____2[3U][168U];
      memcpy(uu____2, randomness, (size_t)3U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_bb4(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[3U][272U];
  memcpy(uu____3, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = closure_791(uu____3[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_a21(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  closure_b81(A_transpose[i]););
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      uint8_t uu____0[34U];
      memcpy(uu____0, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[3U][34U]; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          memcpy(seeds[i], uu____0, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      uint8_t uu____1[3U][34U];
      memcpy(uu____1, seeds, (size_t)3U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[3U];
      sample_from_xof_b01(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)3U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
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
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_1c2(uint8_t (*input)[33U],
                                      uint8_t ret[3U][128U]) {
  uint8_t out[3U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void PRFxN_a9_512(uint8_t (*input)[33U],
                                         uint8_t ret[3U][128U]) {
  PRFxN_1c2(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_2_c1(Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 <
       core_slice___Slice_T___len(randomness, uint8_t, size_t) / (size_t)4U;
       i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice2(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t, Eurydice_slice);
    uint32_t random_bits_as_u32 =
        (((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                         uint8_t *, uint8_t) |
          (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                         uint8_t *, uint8_t)
              << 8U) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                        uint8_t *, uint8_t)
             << 16U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U, uint8_t,
                                       uint8_t *, uint8_t)
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
  return from_i16_array_89_10(Eurydice_array_to_slice(
      (size_t)256U, sampled_i16s, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_3_43(Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 <
       core_slice___Slice_T___len(randomness, uint8_t, size_t) / (size_t)3U;
       i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice2(
        randomness, chunk_number * (size_t)3U,
        chunk_number * (size_t)3U + (size_t)3U, uint8_t, Eurydice_slice);
    uint32_t random_bits_as_u24 =
        ((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                        uint8_t *, uint8_t) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                        uint8_t *, uint8_t)
             << 8U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                       uint8_t *, uint8_t)
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
  return from_i16_array_89_10(Eurydice_array_to_slice(
      (size_t)256U, sampled_i16s, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_470(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_c1(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_45(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    core_core_arch_x86___m256i t =
        libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
            re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_avx2_sub_ea(re->coefficients[j], &t);
    re->coefficients[j] =
        libcrux_ml_kem_vector_avx2_add_ea(re->coefficients[j], &t);
  }
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
static core_core_arch_x86___m256i montgomery_multiply_fe_9d(
    core_core_arch_x86___m256i v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
ntt_layer_int_vec_step_f4(core_core_arch_x86___m256i a,
                          core_core_arch_x86___m256i b, int16_t zeta_r) {
  core_core_arch_x86___m256i t = montgomery_multiply_fe_9d(b, zeta_r);
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
static KRML_MUSTINLINE void ntt_at_layer_4_plus_65(
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
          ntt_layer_int_vec_step_f4(
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
static KRML_MUSTINLINE void ntt_at_layer_3_b4(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]););
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_7c(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(
          re->coefficients[round],
          libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
          libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                             (size_t)1U]);
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_c2(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
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
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_89_99(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    self->coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_ea(self->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_b5(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  ntt_at_layer_7_45(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_b4(&zeta_i, re);
  ntt_at_layer_2_7c(&zeta_i, re);
  ntt_at_layer_1_c2(&zeta_i, re);
  poly_barrett_reduce_89_99(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_b00 sample_vector_cbd_then_ntt_151(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[3U][128U];
  PRFxN_a9_512(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_470(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_b5(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[3U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
ntt_multiply_89_48(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 out = ZERO_89_d5();
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
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_89_971(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(
           Eurydice_array_to_slice((size_t)16U, self->coefficients,
                                   core_core_arch_x86___m256i, Eurydice_slice),
           core_core_arch_x86___m256i, size_t);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_ea(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static core_core_arch_x86___m256i to_standard_domain_42(
    core_core_arch_x86___m256i v) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_89_ac(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        to_standard_domain_42(self->coefficients[j]);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_f01(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)3U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_971(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
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
static tuple_9b0 generate_keypair_unpacked_6c1(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_681(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[3U][3U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed_for_A0, ret);
  sample_matrix_A_a21(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____2 = sample_vector_cbd_then_ntt_151(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_151(uu____3, domain_separator).fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  compute_As_plus_e_f01(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____4[3U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U][3U];
  memcpy(uu____5, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____7[3U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_9b0){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
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
static void closure_e31(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_d5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_d2 clone_d5_48(
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
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_a9
with const generics
- K= 3
*/
static KRML_MUSTINLINE void H_a9_651(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
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
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_831(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_9b0 uu____0 = generate_keypair_unpacked_6c1(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, closure_e31(A[i]););
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_d5_48(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[3U][3U];
  memcpy(uu____2, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t pk_serialized[1184U];
  serialize_public_key_d01(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_651(Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t,
                                   Eurydice_slice),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
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
static libcrux_ml_kem_utils_extraction_helper_Keypair768 generate_keypair_e11(
    Eurydice_slice key_generation_seed) {
  tuple_9b0 uu____0 = generate_keypair_unpacked_6c1(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 pk = uu____0.snd;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_d01(pk.t_as_ntt,
                           Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                   uint8_t, Eurydice_slice),
                           public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key_ae1(sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[1152U];
  memcpy(uu____1, secret_key_serialized, (size_t)1152U * sizeof(uint8_t));
  uint8_t uu____2[1184U];
  memcpy(uu____2, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair768 lit;
  memcpy(lit.fst, uu____1, (size_t)1152U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_751(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, uu____1,
          uu____2 + core_slice___Slice_T___len(private_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____3, uu____4,
          uu____5 + core_slice___Slice_T___len(public_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice);
  uint8_t ret0[32U];
  H_a9_651(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + core_slice___Slice_T___len(implicit_rejection_value,
                                               uint8_t, size_t),
          uint8_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
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
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_c23(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_e11(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key_751(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[2400U];
  memcpy(uu____1, secret_key_serialized, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_05_a70(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  uint8_t uu____3[1184U];
  memcpy(uu____3, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_c90(
      uu____2, libcrux_ml_kem_types_from_b6_4c0(uu____3));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_b00
sample_ring_element_cbd_471(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[3U][128U];
  PRFxN_a9_512(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_470(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[3U];
  memcpy(
      uu____2, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_b00 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_420(Eurydice_slice input, uint8_t ret[128U]) {
  uint8_t digest[128U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t, Eurydice_slice),
      input);
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
static KRML_MUSTINLINE void PRF_a9_934(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_420(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_78(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
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
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_ba(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)1U]);
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_1f(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]););
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
inv_ntt_layer_int_vec_step_reduce_df(core_core_arch_x86___m256i a,
                                     core_core_arch_x86___m256i b,
                                     int16_t zeta_r) {
  core_core_arch_x86___m256i a_minus_b =
      libcrux_ml_kem_vector_avx2_sub_ea(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
      libcrux_ml_kem_vector_avx2_add_ea(a, &b));
  b = montgomery_multiply_fe_9d(a_minus_b, zeta_r);
  return (CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_a2(
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
          inv_ntt_layer_int_vec_step_reduce_df(
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
static KRML_MUSTINLINE void invert_ntt_montgomery_571(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_78(&zeta_i, re);
  invert_ntt_at_layer_2_ba(&zeta_i, re);
  invert_ntt_at_layer_3_1f(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_99(re);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_89_91(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            self->coefficients[j], (int16_t)1441);
    self->coefficients[j] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form,
                                          &error->coefficients[j]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_001(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_971(&result[i1], &product);
    }
    invert_ntt_montgomery_571(&result[i1]);
    add_error_reduce_89_91(&result[i1], &error_1[i1]);
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
static core_core_arch_x86___m256i decompress_1_91(
    core_core_arch_x86___m256i v) {
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
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_message_b9(uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      core_core_arch_x86___m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_deserialize_1_ea(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U, uint8_t,
                                          Eurydice_slice));
      re.coefficients[i0] = decompress_1_91(coefficient_compressed););
  return re;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
add_message_error_reduce_89_67(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            result.coefficients[i0], (int16_t)1441);
    core_core_arch_x86___m256i tmp = libcrux_ml_kem_vector_avx2_add_ea(
        self->coefficients[i0], &message->coefficients[i0]);
    core_core_arch_x86___m256i tmp0 =
        libcrux_ml_kem_vector_avx2_add_ea(coefficient_normal_form, &tmp);
    result.coefficients[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_ea(tmp0);
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
compute_ring_element_v_711(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_971(&result, &product););
  invert_ntt_montgomery_571(&result);
  result = add_message_error_reduce_89_67(error_2, message, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
compress_ciphertext_coefficient_8a(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 10
*/
static core_core_arch_x86___m256i compress_ea_80(
    core_core_arch_x86___m256i vector) {
  return compress_ciphertext_coefficient_8a(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_2f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        compress_ea_80(to_unsigned_representative_a4(re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2_serialize_10_ea(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)20U * i0, (size_t)20U * i0 + (size_t)20U, uint8_t,
        Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)20U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
compress_ciphertext_coefficient_8a0(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 11
*/
static core_core_arch_x86___m256i compress_ea_800(
    core_core_arch_x86___m256i vector) {
  return compress_ciphertext_coefficient_8a0(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_b2(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_2f(re, uu____0);
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
static void compress_then_serialize_u_841(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t,
        Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_b2(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
compress_ciphertext_coefficient_8a1(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 4
*/
static core_core_arch_x86___m256i compress_ea_801(
    core_core_arch_x86___m256i vector) {
  return compress_ciphertext_coefficient_8a1(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_b7(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        compress_ea_801(to_unsigned_representative_a4(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2_serialize_4_ea(coefficient, bytes);
    core_slice___Slice_T___copy_from_slice(
        Eurydice_slice_subslice2(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
compress_ciphertext_coefficient_8a2(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_ea
with const generics
- COEFFICIENT_BITS= 5
*/
static core_core_arch_x86___m256i compress_ea_802(
    core_core_arch_x86___m256i vector) {
  return compress_ciphertext_coefficient_8a2(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_35(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficients =
        compress_ea_802(to_unsigned_representative_a4(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2_serialize_5_ea(coefficients, bytes);
    core_slice___Slice_T___copy_from_slice(
        Eurydice_slice_subslice2(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t,
                                 Eurydice_slice),
        Eurydice_array_to_slice((size_t)10U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_39(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_4_b7(re, out);
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
static void encrypt_unpacked_881(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____1 = sample_vector_cbd_then_ntt_151(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____3 = sample_ring_element_cbd_471(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_934(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_470(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[3U];
  compute_vector_u_001(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_b9(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_711(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_841(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_39(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
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
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_unpacked_1e1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, public_key->public_key_hash, uint8_t,
                              Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_681(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_unpacked_881(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types_from_01_f50(uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_3c lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void entropy_preprocess_af_e21(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1152
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d3(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
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
static void encrypt_fb1(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1088U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[3U];
  deserialize_ring_elements_reduced_5d3(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[3U][3U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed, ret0);
  sample_matrix_A_a21(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1[3U][3U];
  memcpy(uu____1, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[3U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1088U];
  encrypt_unpacked_881(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void kdf_af_501(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
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
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_821(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_e21(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_a9_651(Eurydice_array_to_slice(
               (size_t)1184U, libcrux_ml_kem_types_as_slice_cb_f20(public_key),
               uint8_t, Eurydice_slice),
           ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_681(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_cb_f20(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_fb1(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_01_f50(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_501(shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_3c lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
decompress_ciphertext_coefficient_55(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 10
*/
static core_core_arch_x86___m256i decompress_ciphertext_coefficient_ea_1d(
    core_core_arch_x86___m256i vector) {
  return decompress_ciphertext_coefficient_55(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_10_a7(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)20U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t,
        Eurydice_slice);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_10_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_1d(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
decompress_ciphertext_coefficient_550(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 11
*/
static core_core_arch_x86___m256i decompress_ciphertext_coefficient_ea_1d0(
    core_core_arch_x86___m256i vector) {
  return decompress_ciphertext_coefficient_550(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_11_8d(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)22U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t,
        Eurydice_slice);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_11_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_1d0(coefficient);
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
deserialize_then_decompress_ring_element_u_10(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_a7(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_fe(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_b4(&zeta_i, re);
  ntt_at_layer_2_7c(&zeta_i, re);
  ntt_at_layer_1_c2(&zeta_i, re);
  poly_barrett_reduce_89_99(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_b51(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
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
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_then_decompress_ring_element_u_10(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_fe(&u_as_ntt[i0]);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
decompress_ciphertext_coefficient_551(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 4
*/
static core_core_arch_x86___m256i decompress_ciphertext_coefficient_ea_1d1(
    core_core_arch_x86___m256i vector) {
  return decompress_ciphertext_coefficient_551(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_4_9a(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)8U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t,
        Eurydice_slice);
    core_core_arch_x86___m256i coefficient =
        libcrux_ml_kem_vector_avx2_deserialize_4_ea(bytes);
    re.coefficients[i0] = decompress_ciphertext_coefficient_ea_1d1(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE core_core_arch_x86___m256i
decompress_ciphertext_coefficient_552(core_core_arch_x86___m256i vector) {
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
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_ea with const
generics
- COEFFICIENT_BITS= 5
*/
static core_core_arch_x86___m256i decompress_ciphertext_coefficient_ea_1d2(
    core_core_arch_x86___m256i vector) {
  return decompress_ciphertext_coefficient_552(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_5_75(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)10U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t,
        Eurydice_slice);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_ea(bytes);
    re.coefficients[i0] =
        decompress_ciphertext_coefficient_ea_1d2(re.coefficients[i0]);
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
deserialize_then_decompress_ring_element_v_5b(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_9a(serialized);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
subtract_reduce_89_63(libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
            b.coefficients[i0], (int16_t)1441);
    b.coefficients[i0] = libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
        libcrux_ml_kem_vector_avx2_sub_ea(self->coefficients[i0],
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
compute_message_221(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_971(&result, &product););
  invert_ntt_montgomery_571(&result);
  result = subtract_reduce_89_63(v, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_ec(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      core_core_arch_x86___m256i coefficient =
          to_unsigned_representative_a4(re.coefficients[i0]);
      core_core_arch_x86___m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_ea(coefficient);
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_avx2_serialize_1_ea(coefficient_compressed, bytes);
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          serialized, (size_t)2U * i0, (size_t)2U * i0 + (size_t)2U, uint8_t,
          Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_slice((size_t)2U, bytes, uint8_t, Eurydice_slice),
          uint8_t, void *););
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
static void decrypt_unpacked_8c1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[3U];
  deserialize_then_decompress_u_b51(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_5b(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_221(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ec(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_42(Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t, Eurydice_slice),
      input);
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
static KRML_MUSTINLINE void PRF_a9_933(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_42(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_b21(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_8c1(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_681(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_2d3(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_ed0(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_933(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_unpacked_881(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_ed0(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t,
                                  Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_to_uncompressed_ring_element_63(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = ZERO_89_d5();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t,
        Eurydice_slice);
    re.coefficients[i0] = libcrux_ml_kem_vector_avx2_deserialize_12_ea(bytes);
  }
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_secret_key_201(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_63(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
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
static void decrypt_391(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[3U];
  deserialize_secret_key_201(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[3U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_8c1(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
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
void libcrux_ml_kem_ind_cca_decapsulate_c41(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t,
                              Eurydice_slice),
      (size_t)1152U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = core_slice___Slice_T___split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt_391(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_681(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_2d3(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_ed0(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_933(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_fb1(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_501(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_501(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_ed0(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1568
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d2(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
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
static KRML_MUSTINLINE void serialize_secret_key_ae0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[1536U]) {
  uint8_t out[1536U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_92(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)1536U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_d00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(public_key_serialized, (size_t)0U,
                                  (size_t)1536U, uint8_t, Eurydice_slice);
  uint8_t ret0[1536U];
  serialize_secret_key_ae0(t_as_ntt, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)1536U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key_serialized,
                                      (size_t)1536U, uint8_t, size_t,
                                      Eurydice_slice),
      seed_for_a, uint8_t, void *);
  memcpy(ret, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_cf0(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  deserialize_ring_elements_reduced_5d2(
      Eurydice_array_to_subslice_to((size_t)1568U, public_key, (size_t)1536U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_d00(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1568U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$4size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$4size_t]]

*/
typedef struct tuple_54_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 snd;
} tuple_54;

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 4
*/
static KRML_MUSTINLINE void G_a9_680(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static void closure_b80(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_4d0(uint8_t input[4U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[3U], uint8_t, Eurydice_slice));
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
shake128_init_absorb_final_a9_ca0(uint8_t input[4U][34U]) {
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_4d0(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_6b0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[4U][504U]) {
  uint8_t out[4U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_4d0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_first_three_blocks_6b0(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb1(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_1b0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[4U][168U]) {
  uint8_t out[4U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_5a0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_next_block_1b0(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb2(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_790(
    int16_t s[272U]) {
  return from_i16_array_89_10(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_b00(
    uint8_t seeds[4U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, seeds, (size_t)4U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_ca0(uu____0);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_first_three_blocks_a9_4d0(&xof_state, randomness0);
  uint8_t uu____1[4U][504U];
  memcpy(uu____1, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_bb1(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      shake128_squeeze_next_block_a9_5a0(&xof_state, randomness);
      uint8_t uu____2[4U][168U];
      memcpy(uu____2, randomness, (size_t)4U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_bb2(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[4U][272U];
  memcpy(uu____3, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = closure_790(uu____3[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_a20(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U][4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  closure_b80(A_transpose[i]););
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      uint8_t uu____0[34U];
      memcpy(uu____0, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[4U][34U]; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          memcpy(seeds[i], uu____0, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      uint8_t uu____1[4U][34U];
      memcpy(uu____1, seeds, (size_t)4U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[4U];
      sample_from_xof_b00(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)4U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
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
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_1c1(uint8_t (*input)[33U],
                                      uint8_t ret[4U][128U]) {
  uint8_t out[4U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[3U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void PRFxN_a9_511(uint8_t (*input)[33U],
                                         uint8_t ret[4U][128U]) {
  PRFxN_1c1(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_71 sample_vector_cbd_then_ntt_150(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[4U][128U];
  PRFxN_a9_511(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_470(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_b5(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[4U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_89_970(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(
           Eurydice_array_to_slice((size_t)16U, self->coefficients,
                                   core_core_arch_x86___m256i, Eurydice_slice),
           core_core_arch_x86___m256i, size_t);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_ea(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_f00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)4U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_970(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static tuple_54 generate_keypair_unpacked_6c0(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_680(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[4U][4U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed_for_A0, ret);
  sample_matrix_A_a20(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____2 = sample_vector_cbd_then_ntt_150(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[4U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_150(uu____3, domain_separator).fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  compute_As_plus_e_f00(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____4[4U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[4U][4U];
  memcpy(uu____5, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____7[4U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_54){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
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
static void closure_e30(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
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
static KRML_MUSTINLINE void H_a9_650(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
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
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_830(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_54 uu____0 = generate_keypair_unpacked_6c0(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, closure_e30(A[i]););
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_d5_48(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[4U][4U];
  memcpy(uu____2, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  uint8_t pk_serialized[1568U];
  serialize_public_key_d00(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_650(Eurydice_array_to_slice((size_t)1568U, pk_serialized, uint8_t,
                                   Eurydice_slice),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_01 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair1024 generate_keypair_e10(
    Eurydice_slice key_generation_seed) {
  tuple_54 uu____0 = generate_keypair_unpacked_6c0(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 pk = uu____0.snd;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_d00(pk.t_as_ntt,
                           Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                   uint8_t, Eurydice_slice),
                           public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key_ae0(sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[1536U];
  memcpy(uu____1, secret_key_serialized, (size_t)1536U * sizeof(uint8_t));
  uint8_t uu____2[1568U];
  memcpy(uu____2, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 lit;
  memcpy(lit.fst, uu____1, (size_t)1536U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_750(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[3168U]) {
  uint8_t out[3168U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, uu____1,
          uu____2 + core_slice___Slice_T___len(private_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____3, uu____4,
          uu____5 + core_slice___Slice_T___len(public_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice);
  uint8_t ret0[32U];
  H_a9_650(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + core_slice___Slice_T___len(implicit_rejection_value,
                                               uint8_t, size_t),
          uint8_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
  memcpy(ret, out, (size_t)3168U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_c22(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_e10(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key_750(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[3168U];
  memcpy(uu____1, secret_key_serialized, (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_95 private_key =
      libcrux_ml_kem_types_from_05_a71(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_95 uu____2 = private_key;
  uint8_t uu____3[1568U];
  memcpy(uu____3, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_c91(
      uu____2, libcrux_ml_kem_types_from_b6_4c1(uu____3));
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
sample_ring_element_cbd_470(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[4U][128U];
  PRFxN_a9_511(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_470(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[4U];
  memcpy(
      uu____2, error_1,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_71 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
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
static KRML_MUSTINLINE void PRF_a9_932(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_420(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_570(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_78(&zeta_i, re);
  invert_ntt_at_layer_2_ba(&zeta_i, re);
  invert_ntt_at_layer_3_1f(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_99(re);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_000(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)4U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_970(&result[i1], &product);
    }
    invert_ntt_montgomery_570(&result[i1]);
    add_error_reduce_89_91(&result[i1], &error_1[i1]);
  }
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
compute_ring_element_v_710(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_970(&result, &product););
  invert_ntt_montgomery_570(&result);
  result = add_message_error_reduce_89_67(error_2, message, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_d10(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i coefficient =
        compress_ea_800(to_unsigned_representative_a4(re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2_serialize_11_ea(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)22U * i0, (size_t)22U * i0 + (size_t)22U, uint8_t,
        Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)22U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
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
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_b20(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_d10(re, uu____0);
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
static void compress_then_serialize_u_840(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[4U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t,
        Eurydice_slice);
    uint8_t ret[352U];
    compress_then_serialize_ring_element_u_b20(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)352U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_390(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re, Eurydice_slice out) {
  compress_then_serialize_5_35(re, out);
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
static void encrypt_unpacked_880(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____1 = sample_vector_cbd_then_ntt_150(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____3 = sample_ring_element_cbd_470(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[4U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_932(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_470(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[4U];
  compute_vector_u_000(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_b9(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_710(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[1568U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[4U];
  memcpy(
      uu____5, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_840(
      uu____5,
      Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)1408U,
                                  uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_390(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
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
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_unpacked_1e0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, public_key->public_key_hash, uint8_t,
                              Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_680(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_unpacked_880(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 =
      libcrux_ml_kem_types_from_01_f51(uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_21 lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void entropy_preprocess_af_e20(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 1536
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d1(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
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
static void encrypt_fb0(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1568U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  deserialize_ring_elements_reduced_5d1(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed, ret0);
  sample_matrix_A_a20(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[4U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1[4U][4U];
  memcpy(uu____1, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[4U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1568U];
  encrypt_unpacked_880(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1568U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE void kdf_af_500(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
with const generics
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
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_820(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_e20(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_a9_650(Eurydice_array_to_slice(
               (size_t)1568U, libcrux_ml_kem_types_as_slice_cb_f21(public_key),
               uint8_t, Eurydice_slice),
           ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_680(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_cb_f21(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_fb0(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_01_f51(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_500(shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_21 lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
deserialize_then_decompress_ring_element_u_100(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_8d(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_fe0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_65(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_b4(&zeta_i, re);
  ntt_at_layer_2_7c(&zeta_i, re);
  ntt_at_layer_1_c2(&zeta_i, re);
  poly_barrett_reduce_89_99(re);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_b50(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
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
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_then_decompress_ring_element_u_100(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_fe0(&u_as_ntt[i0]);
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
deserialize_then_decompress_ring_element_v_5b0(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_75(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
compute_message_220(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_970(&result, &product););
  invert_ntt_montgomery_570(&result);
  result = subtract_reduce_89_63(v, result);
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
static void decrypt_unpacked_8c0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[4U];
  deserialize_then_decompress_u_b50(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_5b0(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_220(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ec(message, ret0);
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
static KRML_MUSTINLINE void PRF_a9_931(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_42(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_b20(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_8c0(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_680(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_2d4(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_ed1(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_931(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_unpacked_880(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_ed1(ciphertext),
          Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t,
                                  Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_secret_key_200(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_63(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
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
static void decrypt_390(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
  deserialize_secret_key_200(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[4U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_8c0(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
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
void libcrux_ml_kem_ind_cca_decapsulate_c40(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t,
                              Eurydice_slice),
      (size_t)1536U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      secret_key0, (size_t)1568U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = core_slice___Slice_T___split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt_390(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_680(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_2d4(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_ed1(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_931(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_fb0(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_500(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_500(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_ed1(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 800
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
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
static KRML_MUSTINLINE void serialize_secret_key_ae(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *key,
    uint8_t ret[768U]) {
  uint8_t out[768U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)2U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_92(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)768U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)768U, uint8_t, Eurydice_slice);
  uint8_t ret0[768U];
  serialize_secret_key_ae(t_as_ntt, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)768U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from((size_t)800U, public_key_serialized,
                                      (size_t)768U, uint8_t, size_t,
                                      Eurydice_slice),
      seed_for_a, uint8_t, void *);
  memcpy(ret, public_key_serialized, (size_t)800U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_cf(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  deserialize_ring_elements_reduced_5d0(
      Eurydice_array_to_subslice_to((size_t)800U, public_key, (size_t)768U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key_d0(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)800U, public_key, (size_t)768U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)800U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$2size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$2size_t]]

*/
typedef struct tuple_4c_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 snd;
} tuple_4c;

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_a9
with const generics
- K= 2
*/
static KRML_MUSTINLINE void G_a9_68(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_avx2_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static void closure_b8(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb_final_4d(uint8_t input[2U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_29 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice));
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
shake128_init_absorb_final_a9_ca(uint8_t input[2U][34U]) {
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_final_4d(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_6b(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[2U][504U]) {
  uint8_t out[2U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_a9_4d(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_first_three_blocks_6b(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_1b(
    libcrux_sha3_avx2_x4_incremental_KeccakState *st, uint8_t ret[2U][168U]) {
  uint8_t out[2U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void shake128_squeeze_next_block_a9_5a(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_next_block_1b(self, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_bb0(
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
              uint8_t, Eurydice_slice);
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_ea(
              uu____0, Eurydice_array_to_subslice2(
                           out[i1], sampled_coefficients[i1],
                           sampled_coefficients[i1] + (size_t)16U, int16_t,
                           Eurydice_slice));
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
static libcrux_ml_kem_polynomial_PolynomialRingElement_d2 closure_79(
    int16_t s[272U]) {
  return from_i16_array_89_10(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_from_xof_b0(
    uint8_t seeds[2U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, seeds, (size_t)2U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb_final_a9_ca(uu____0);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_first_three_blocks_a9_4d(&xof_state, randomness0);
  uint8_t uu____1[2U][504U];
  memcpy(uu____1, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_bb(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      shake128_squeeze_next_block_a9_5a(&xof_state, randomness);
      uint8_t uu____2[2U][168U];
      memcpy(uu____2, randomness, (size_t)2U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_bb0(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[2U][272U];
  memcpy(uu____3, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = closure_79(uu____3[i]););
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
static KRML_MUSTINLINE void sample_matrix_A_a2(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U][2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  closure_b8(A_transpose[i]););
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      uint8_t uu____0[34U];
      memcpy(uu____0, seed, (size_t)34U * sizeof(uint8_t));
      uint8_t seeds[2U][34U]; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          memcpy(seeds[i], uu____0, (size_t)34U * sizeof(uint8_t)););
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      uint8_t uu____1[2U][34U];
      memcpy(uu____1, seeds, (size_t)2U * sizeof(uint8_t[34U]));
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sampled[2U];
      sample_from_xof_b0(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)2U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_d2 sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
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
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_1c(uint8_t (*input)[33U],
                                     uint8_t ret[2U][192U]) {
  uint8_t out[2U][192U] = {{0U}};
  uint8_t out0[192U] = {0U};
  uint8_t out1[192U] = {0U};
  uint8_t out2[192U] = {0U};
  uint8_t out3[192U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void PRFxN_a9_51(uint8_t (*input)[33U],
                                        uint8_t ret[2U][192U]) {
  PRFxN_1c(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_d2
sample_from_binomial_distribution_47(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_43(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE tuple_74 sample_vector_cbd_then_ntt_15(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[2U][192U];
  PRFxN_a9_51(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_47(Eurydice_array_to_slice(
              (size_t)192U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_b5(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[2U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_89_97(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *rhs) {
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(
           Eurydice_array_to_slice((size_t)16U, self->coefficients,
                                   core_core_arch_x86___m256i, Eurydice_slice),
           core_core_arch_x86___m256i, size_t);
       i++) {
    size_t i0 = i;
    self->coefficients[i0] = libcrux_ml_kem_vector_avx2_add_ea(
        self->coefficients[i0], &rhs->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_As_plus_e_f0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)2U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_97(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static tuple_4c generate_keypair_unpacked_6c(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_a9_68(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A_transpose[2U][2U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed_for_A0, ret);
  sample_matrix_A_a2(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____2 = sample_vector_cbd_then_ntt_15(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_as_ntt[2U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_15(uu____3, domain_separator).fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  compute_As_plus_e_f0(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____4[2U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[2U][2U];
  memcpy(uu____5, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____7[2U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  return (CLITERAL(tuple_4c){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
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
static void closure_e3(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_89_d5(););
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
static KRML_MUSTINLINE void H_a9_65(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_avx2_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
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
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_83(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_4c uu____0 = generate_keypair_unpacked_6c(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, closure_e3(A[i]););
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
              clone_d5_48(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[2U][2U];
  memcpy(uu____2, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  uint8_t pk_serialized[800U];
  serialize_public_key_d0(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_a9_65(Eurydice_array_to_slice((size_t)800U, pk_serialized, uint8_t,
                                  Eurydice_slice),
          public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d6 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair512 generate_keypair_e1(
    Eurydice_slice key_generation_seed) {
  tuple_4c uu____0 = generate_keypair_unpacked_6c(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 pk = uu____0.snd;
  uint8_t public_key_serialized[800U];
  serialize_public_key_d0(pk.t_as_ntt,
                          Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                  uint8_t, Eurydice_slice),
                          public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key_ae(sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[768U];
  memcpy(uu____1, secret_key_serialized, (size_t)768U * sizeof(uint8_t));
  uint8_t uu____2[800U];
  memcpy(uu____2, public_key_serialized, (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair512 lit;
  memcpy(lit.fst, uu____1, (size_t)768U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)800U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_75(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[1632U]) {
  uint8_t out[1632U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, uu____1,
          uu____2 + core_slice___Slice_T___len(private_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____3, uu____4,
          uu____5 + core_slice___Slice_T___len(public_key, uint8_t, size_t),
          uint8_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
      out, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice);
  uint8_t ret0[32U];
  H_a9_65(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____7, uu____8,
          uu____9 + core_slice___Slice_T___len(implicit_rejection_value,
                                               uint8_t, size_t),
          uint8_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
  memcpy(ret, out, (size_t)1632U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_ind_cca_generate_keypair_c2(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_e1(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key_75(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[1632U];
  memcpy(uu____1, secret_key_serialized, (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_5e private_key =
      libcrux_ml_kem_types_from_05_a7(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_5e uu____2 = private_key;
  uint8_t uu____3[800U];
  memcpy(uu____3, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_c9(
      uu____2, libcrux_ml_kem_types_from_b6_4c(uu____3));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_1c0(uint8_t (*input)[33U],
                                      uint8_t ret[2U][128U]) {
  uint8_t out[2U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out3, uint8_t, Eurydice_slice));
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
static KRML_MUSTINLINE void PRFxN_a9_510(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_1c0(input, ret);
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
sample_ring_element_cbd_47(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_89_d5(););
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      memcpy(prf_inputs[i], uu____0, (size_t)33U * sizeof(uint8_t)););
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  uint8_t prf_outputs[2U][128U];
  PRFxN_a9_510(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1 =
          sample_from_binomial_distribution_470(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____2[2U];
  memcpy(
      uu____2, error_1,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  tuple_74 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  lit.snd = domain_separator;
  return lit;
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
static KRML_MUSTINLINE void PRF_a9_930(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_420(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_57(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_78(&zeta_i, re);
  invert_ntt_at_layer_2_ba(&zeta_i, re);
  invert_ntt_at_layer_3_1f(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_a2(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_99(re);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_vector_u_00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result[i] = ZERO_89_d5(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)2U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
          ntt_multiply_89_48(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_97(&result[i1], &product);
    }
    invert_ntt_montgomery_57(&result[i1]);
    add_error_reduce_89_91(&result[i1], &error_1[i1]);
  }
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
compute_ring_element_v_71(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_97(&result, &product););
  invert_ntt_montgomery_57(&result);
  result = add_message_error_reduce_89_67(error_2, message, result);
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
static void compress_then_serialize_u_84(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 input[2U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)2U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_d2,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_d2, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t,
        Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_b2(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
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
static void encrypt_unpacked_88(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_2d2(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____1 = sample_vector_cbd_then_ntt_15(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_74 uu____3 = sample_ring_element_cbd_47(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_1[2U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_a9_930(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 error_2 =
      sample_from_binomial_distribution_470(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u[2U];
  compute_vector_u_00(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message_as_ring_element =
      deserialize_then_decompress_message_b9(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      compute_ring_element_v_71(public_key->t_as_ntt, r_as_ntt, &error_2,
                                &message_as_ring_element);
  uint8_t ciphertext[768U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____5[2U];
  memcpy(
      uu____5, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  compress_then_serialize_u_84(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)640U,
                                           uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____6 = v;
  compress_then_serialize_ring_element_v_39(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
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
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_unpacked_1e(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, public_key->public_key_hash, uint8_t,
                              Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_unpacked_88(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 =
      libcrux_ml_kem_types_from_01_f5(uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_ec lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void entropy_preprocess_af_e2(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- PUBLIC_KEY_SIZE= 768
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_5d(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice2(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_reduced_ring_element_dd(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
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
static void encrypt_fb(Eurydice_slice public_key, uint8_t message[32U],
                       Eurydice_slice randomness, uint8_t ret[768U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  deserialize_ring_elements_reduced_5d(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_2d1(seed, ret0);
  sample_matrix_A_a2(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[2U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____1[2U][2U];
  memcpy(uu____1, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2[2U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[768U];
  encrypt_unpacked_88(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)768U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE void kdf_af_50(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
with const generics
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
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_82(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_e2(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_a9_65(Eurydice_array_to_slice(
              (size_t)800U, libcrux_ml_kem_types_as_slice_cb_f2(public_key),
              uint8_t, Eurydice_slice),
          ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_cb_f2(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_fb(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 ciphertext0 =
      libcrux_ml_kem_types_from_01_f5(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_50(shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_ec lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_b5(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)768U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
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
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_then_decompress_ring_element_u_10(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_fe(&u_as_ntt[i0]);
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
compute_message_22(
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 result = ZERO_89_d5();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 product =
                      ntt_multiply_89_48(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_97(&result, &product););
  invert_ntt_montgomery_57(&result);
  result = subtract_reduce_89_63(v, result);
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
static void decrypt_unpacked_8c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 u_as_ntt[2U];
  deserialize_then_decompress_u_b5(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 v =
      deserialize_then_decompress_ring_element_v_5b(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 message =
      compute_message_22(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ec(message, ret0);
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
static KRML_MUSTINLINE void PRF_a9_93(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_42(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_b2(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6 *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_8c(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_2d0(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_ed(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_a9_93(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_unpacked_88(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_ed(ciphertext),
          Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t,
                                  Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_secret_key_20(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_d5(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice2(
        secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0 =
        deserialize_to_uncompressed_ring_element_63(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
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
static void decrypt_39(Eurydice_slice secret_key, uint8_t *ciphertext,
                       uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
  deserialize_secret_key_20(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 uu____0[2U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_d2));
  uint8_t ret0[32U];
  decrypt_unpacked_8c(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_ind_cca_MlKem
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
void libcrux_ml_kem_ind_cca_decapsulate_c4(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t,
                              Eurydice_slice),
      (size_t)768U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      secret_key0, (size_t)800U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = core_slice___Slice_T___split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt_39(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_2d(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_a9_68(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_2d0(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_ed(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_a9_93(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_fb(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_50(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_50(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_ed(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}
