/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 8db8a4838ea46c9ac681ba1051d1d296dd0d54b7
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8
 * Libcrux: d992e8bff91dab77b6f0abebf16384ce422b310c
 */

#include "internal/libcrux_mlkem_avx2.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"

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

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_zero(void) {
  return libcrux_intrinsics_avx2_extract_mm256_setzero_si256();
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO(
    void) {
  return libcrux_ml_kem_vector_avx2_zero();
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array) {
  return libcrux_intrinsics_avx2_extract_mm256_loadu_si256_i16(array);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___from_i16_array(
    Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_i16_array(uint8_t v,
                                                             int16_t ret[16U]) {
  int16_t output[16U] = {0U};
  libcrux_intrinsics_avx2_extract_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, output, int16_t, Eurydice_slice), v);
  memcpy(ret, output, (size_t)16U * sizeof(int16_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___to_i16_array(
    uint8_t x, int16_t ret[16U]) {
  int16_t ret0[16U];
  libcrux_ml_kem_vector_avx2_to_i16_array(x, ret0);
  memcpy(ret, ret0, (size_t)16U * sizeof(int16_t));
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_arithmetic_add(uint8_t lhs,
                                                                  uint8_t rhs) {
  return libcrux_intrinsics_avx2_extract_mm256_add_epi16(lhs, rhs);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
    uint8_t lhs, uint8_t *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_arithmetic_sub(uint8_t lhs,
                                                                  uint8_t rhs) {
  return libcrux_intrinsics_avx2_extract_mm256_sub_epi16(lhs, rhs);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
    uint8_t lhs, uint8_t *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs[0U]);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(uint8_t vector,
                                                           int16_t constant) {
  uint8_t uu____0 = vector;
  return libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(constant));
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___multiply_by_constant(
    uint8_t v, int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(v, c);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    uint8_t vector, int16_t constant) {
  uint8_t uu____0 = vector;
  return libcrux_intrinsics_avx2_extract_mm256_and_si256(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(constant));
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___bitwise_and_with_constant(
    uint8_t vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vector, constant);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(uint8_t vector) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t v_minus_field_modulus =
      libcrux_intrinsics_avx2_extract_mm256_sub_epi16(vector, field_modulus);
  uint8_t sign_mask = libcrux_intrinsics_avx2_extract_mm256_srai_epi16(
      (int32_t)15, v_minus_field_modulus, uint8_t);
  uint8_t conditional_add_field_modulus =
      libcrux_intrinsics_avx2_extract_mm256_and_si256(sign_mask, field_modulus);
  return libcrux_intrinsics_avx2_extract_mm256_add_epi16(
      v_minus_field_modulus, conditional_add_field_modulus);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___cond_subtract_3329(
    uint8_t vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(uint8_t vector) {
  uint8_t uu____0 = vector;
  uint8_t t = libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                   LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  uint8_t uu____1 = t;
  uint8_t t0 = libcrux_intrinsics_avx2_extract_mm256_add_epi16(
      uu____1, libcrux_intrinsics_avx2_extract_mm256_set1_epi16((int16_t)512));
  uint8_t quotient = libcrux_intrinsics_avx2_extract_mm256_srai_epi16(
      (int32_t)10, t0, uint8_t);
  uint8_t uu____2 = quotient;
  uint8_t quotient_times_field_modulus =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
          uu____2, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                       LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return libcrux_intrinsics_avx2_extract_mm256_sub_epi16(
      vector, quotient_times_field_modulus);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
    uint8_t vector) {
  return libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vector);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    uint8_t vector, int16_t constant) {
  uint8_t constant0 =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi16(constant);
  uint8_t value_low =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(vector, constant0);
  uint8_t uu____0 = value_low;
  uint8_t k = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  uint8_t uu____1 = k;
  uint8_t k_times_modulus = libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(
      uu____1, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                   LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  uint8_t value_high =
      libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(vector, constant0);
  return libcrux_intrinsics_avx2_extract_mm256_sub_epi16(value_high,
                                                         k_times_modulus);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
    uint8_t vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    uint8_t vector) {
  uint8_t field_modulus_halved =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
          (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) /
          (int16_t)2);
  uint8_t field_modulus_quartered =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
          (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) /
          (int16_t)4);
  uint8_t shifted = libcrux_intrinsics_avx2_extract_mm256_sub_epi16(
      field_modulus_halved, vector);
  uint8_t mask = libcrux_intrinsics_avx2_extract_mm256_srai_epi16(
      (int32_t)15, shifted, uint8_t);
  uint8_t shifted_to_positive =
      libcrux_intrinsics_avx2_extract_mm256_xor_si256(mask, shifted);
  uint8_t shifted_to_positive_in_range =
      libcrux_intrinsics_avx2_extract_mm256_sub_epi16(shifted_to_positive,
                                                      field_modulus_quartered);
  return libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
      (int32_t)15, shifted_to_positive_in_range, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___compress_1(
    uint8_t vector) {
  return libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
      vector);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(
    uint8_t lhs, uint8_t rhs) {
  uint8_t prod02 = libcrux_intrinsics_avx2_extract_mm256_mul_epu32(lhs, rhs);
  uint8_t uu____0 = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)245, lhs, uint8_t);
  uint8_t prod13 = libcrux_intrinsics_avx2_extract_mm256_mul_epu32(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
                   (int32_t)245, rhs, uint8_t));
  uint8_t uu____1 =
      libcrux_intrinsics_avx2_extract_mm256_unpacklo_epi32(prod02, prod13);
  return libcrux_intrinsics_avx2_extract_mm256_unpackhi_epi64(
      uu____1,
      libcrux_intrinsics_avx2_extract_mm256_unpackhi_epi32(prod02, prod13));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    uint8_t v, uint8_t c) {
  uint8_t value_low = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(v, c);
  uint8_t uu____0 = value_low;
  uint8_t k = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  uint8_t uu____1 = k;
  uint8_t k_times_modulus = libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(
      uu____1, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                   LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  uint8_t value_high = libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_extract_mm256_sub_epi16(value_high,
                                                         k_times_modulus);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  uint8_t zetas = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1,
      -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)245, vector, uint8_t);
  uint8_t rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)160, vector, uint8_t);
  return libcrux_intrinsics_avx2_extract_mm256_add_epi16(lhs, rhs0);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1) {
  uint8_t zetas = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0,
      -zeta0, -zeta0, -zeta0, zeta0, zeta0, zeta0, zeta0);
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)238, vector, uint8_t);
  uint8_t rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)68, vector, uint8_t);
  return libcrux_intrinsics_avx2_extract_mm256_add_epi16(lhs, rhs0);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    uint8_t v, uint8_t c) {
  uint8_t value_low = libcrux_intrinsics_avx2_extract_mm_mullo_epi16(v, c);
  uint8_t uu____0 = value_low;
  uint8_t k = libcrux_intrinsics_avx2_extract_mm_mullo_epi16(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  uint8_t uu____1 = k;
  uint8_t k_times_modulus = libcrux_intrinsics_avx2_extract_mm_mulhi_epi16(
      uu____1, libcrux_intrinsics_avx2_extract_mm_set1_epi16(
                   LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  uint8_t value_high = libcrux_intrinsics_avx2_extract_mm_mulhi_epi16(v, c);
  return libcrux_intrinsics_avx2_extract_mm_sub_epi16(value_high,
                                                      k_times_modulus);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(uint8_t vector, int16_t zeta) {
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, vector, uint8_t);
  uint8_t uu____0 = rhs;
  uint8_t rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          uu____0, libcrux_intrinsics_avx2_extract_mm_set1_epi16(zeta));
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t lower_coefficients =
      libcrux_intrinsics_avx2_extract_mm_add_epi16(lhs, rhs0);
  uint8_t upper_coefficients =
      libcrux_intrinsics_avx2_extract_mm_sub_epi16(lhs, rhs0);
  uint8_t combined =
      libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(lower_coefficients);
  uint8_t combined0 = libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients, uint8_t);
  return combined0;
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_3_step(
    uint8_t vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)245, vector, uint8_t);
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
      (int32_t)160, vector, uint8_t);
  uint8_t uu____0 = rhs;
  uint8_t rhs0 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_set_epi16(
                   (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                   (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                   (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1,
                   (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1));
  uint8_t sum0 = libcrux_intrinsics_avx2_extract_mm256_add_epi16(lhs, rhs0);
  uint8_t uu____1 = sum0;
  uint8_t sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi16(
                       zeta3, zeta3, (int16_t)0, (int16_t)0, zeta2, zeta2,
                       (int16_t)0, (int16_t)0, zeta1, zeta1, (int16_t)0,
                       (int16_t)0, zeta0, zeta0, (int16_t)0, (int16_t)0));
  uint8_t sum = libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(sum0);
  return libcrux_intrinsics_avx2_extract_mm256_blend_epi16(
      (int32_t)204, sum, sum_times_zetas, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
      vector, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1) {
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)245, vector, uint8_t);
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)160, vector, uint8_t);
  uint8_t uu____0 = rhs;
  uint8_t rhs0 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0, libcrux_intrinsics_avx2_extract_mm256_set_epi16(
                   (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1,
                   (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)-1,
                   (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)1,
                   (int16_t)1, (int16_t)1, (int16_t)1));
  uint8_t sum = libcrux_intrinsics_avx2_extract_mm256_add_epi16(lhs, rhs0);
  uint8_t uu____1 = sum;
  uint8_t sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi16(
                       zeta1, zeta1, zeta1, zeta1, (int16_t)0, (int16_t)0,
                       (int16_t)0, (int16_t)0, zeta0, zeta0, zeta0, zeta0,
                       (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0));
  return libcrux_intrinsics_avx2_extract_mm256_blend_epi16(
      (int32_t)240, sum, sum_times_zetas, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0,
                                                             zeta1);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(
    uint8_t vector, int16_t zeta) {
  uint8_t lhs = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, vector, uint8_t);
  uint8_t rhs = libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t lower_coefficients =
      libcrux_intrinsics_avx2_extract_mm_add_epi16(lhs, rhs);
  uint8_t upper_coefficients =
      libcrux_intrinsics_avx2_extract_mm_sub_epi16(lhs, rhs);
  uint8_t uu____0 = upper_coefficients;
  uint8_t upper_coefficients0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          uu____0, libcrux_intrinsics_avx2_extract_mm_set1_epi16(zeta));
  uint8_t combined =
      libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(lower_coefficients);
  uint8_t combined0 = libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
      (int32_t)1, combined, upper_coefficients0, uint8_t);
  return combined0;
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_3_step(
    uint8_t vector, int16_t zeta) {
  return libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(uint8_t v) {
  uint8_t uu____0 = v;
  uint8_t k = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  uint8_t uu____1 = k;
  uint8_t k_times_modulus = libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(
      uu____1, libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
                   (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  uint8_t value_high =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi32((int32_t)16, v, uint8_t);
  uint8_t result = libcrux_intrinsics_avx2_extract_mm256_sub_epi16(
      value_high, k_times_modulus);
  uint8_t result0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)16, result, uint8_t);
  return libcrux_intrinsics_avx2_extract_mm256_srai_epi32((int32_t)16, result0,
                                                          uint8_t);
}

KRML_MUSTINLINE uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(
    uint8_t lhs, uint8_t rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  uint8_t shuffle_with = libcrux_intrinsics_avx2_extract_mm256_set_epi8(
      (int8_t)15, (int8_t)14, (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6,
      (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8,
      (int8_t)5, (int8_t)4, (int8_t)1, (int8_t)0, (int8_t)15, (int8_t)14,
      (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6, (int8_t)3, (int8_t)2,
      (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
      (int8_t)1, (int8_t)0);
  uint8_t lhs_shuffled =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(lhs, shuffle_with);
  uint8_t lhs_shuffled0 =
      libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
          (int32_t)216, lhs_shuffled, uint8_t);
  uint8_t lhs_evens =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(lhs_shuffled0);
  uint8_t lhs_evens0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(lhs_evens);
  uint8_t lhs_odds = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, lhs_shuffled0, uint8_t);
  uint8_t lhs_odds0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(lhs_odds);
  uint8_t rhs_shuffled =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(rhs, shuffle_with);
  uint8_t rhs_shuffled0 =
      libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
          (int32_t)216, rhs_shuffled, uint8_t);
  uint8_t rhs_evens =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(rhs_shuffled0);
  uint8_t rhs_evens0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(rhs_evens);
  uint8_t rhs_odds = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, rhs_shuffled0, uint8_t);
  uint8_t rhs_odds0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(rhs_odds);
  uint8_t left =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(lhs_evens0, rhs_evens0);
  uint8_t right =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(lhs_odds0, rhs_odds0);
  uint8_t right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(right);
  uint8_t uu____0 = right0;
  uint8_t right1 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm256_set_epi32(
          -(int32_t)zeta3, (int32_t)zeta3, -(int32_t)zeta2, (int32_t)zeta2,
          -(int32_t)zeta1, (int32_t)zeta1, -(int32_t)zeta0, (int32_t)zeta0));
  uint8_t products_left =
      libcrux_intrinsics_avx2_extract_mm256_add_epi32(left, right1);
  uint8_t products_left0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_left);
  uint8_t uu____1 = rhs;
  uint8_t rhs_adjacent_swapped =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi8(
                       (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14,
                       (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10, (int8_t)5,
                       (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0,
                       (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)15,
                       (int8_t)14, (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10,
                       (int8_t)5, (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1,
                       (int8_t)0, (int8_t)3, (int8_t)2));
  uint8_t products_right = libcrux_intrinsics_avx2_extract_mm256_madd_epi16(
      lhs, rhs_adjacent_swapped);
  uint8_t products_right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_right);
  uint8_t products_right1 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)16, products_right0, uint8_t);
  return libcrux_intrinsics_avx2_extract_mm256_blend_epi16(
      (int32_t)170, products_left0, products_right1, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_multiply(
    uint8_t *lhs, uint8_t *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs[0U], rhs[0U], zeta0,
                                                     zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    uint8_t vector, uint8_t ret[2U]) {
  uint8_t lsb_to_msb = libcrux_intrinsics_avx2_extract_mm256_slli_epi16(
      (int32_t)15, vector, uint8_t);
  uint8_t low_msbs =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(lsb_to_msb);
  uint8_t high_msbs = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, lsb_to_msb, uint8_t);
  uint8_t msbs =
      libcrux_intrinsics_avx2_extract_mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = libcrux_intrinsics_avx2_extract_mm_movemask_epi8(msbs);
  uint8_t serialized[2U] = {0U};
  serialized[0U] = (uint8_t)bits_packed;
  serialized[1U] = (uint8_t)(bits_packed >> 8U);
  memcpy(ret, serialized, (size_t)2U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_1(
    uint8_t vector, uint8_t ret[2U]) {
  uint8_t ret0[2U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes) {
  int16_t uu____0 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____1 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____2 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____3 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____4 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____5 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____6 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____7 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____8 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____9 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____10 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____11 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____12 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____13 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____14 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  uint8_t coefficients = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      uu____0, uu____1, uu____2, uu____3, uu____4, uu____5, uu____6, uu____7,
      uu____8, uu____9, uu____10, uu____11, uu____12, uu____13, uu____14,
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                    uint8_t));
  uint8_t shift_lsb_to_msb = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768,
      (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
      (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U, (int16_t)-32768);
  uint8_t coefficients_in_msb =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(coefficients,
                                                        shift_lsb_to_msb);
  return libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
      (int32_t)15, coefficients_in_msb, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_1(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    uint8_t vector, uint8_t ret[8U]) {
  uint8_t serialized[16U] = {0U};
  uint8_t uu____0 = vector;
  uint8_t adjacent_2_combined =
      libcrux_intrinsics_avx2_extract_mm256_madd_epi16(
          uu____0,
          libcrux_intrinsics_avx2_extract_mm256_set_epi16(
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1,
              (int16_t)1 << 4U, (int16_t)1, (int16_t)1 << 4U, (int16_t)1));
  uint8_t uu____1 = adjacent_2_combined;
  uint8_t adjacent_8_combined =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(
          uu____1,
          libcrux_intrinsics_avx2_extract_mm256_set_epi8(
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4,
              (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8,
              (int8_t)4, (int8_t)0));
  uint8_t uu____2 = adjacent_8_combined;
  uint8_t combined = libcrux_intrinsics_avx2_extract_mm256_permutevar8x32_epi32(
      uu____2, libcrux_intrinsics_avx2_extract_mm256_set_epi32(
                   (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
                   (int32_t)0, (int32_t)4, (int32_t)0));
  uint8_t combined0 =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(combined);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t, Eurydice_slice),
      combined0);
  uint8_t ret0[8U];
  core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice((size_t)16U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)8U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      Eurydice_slice, uint8_t[8U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_8size_t__core_array_TryFromSliceError(
      dst, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_4(
    uint8_t vector, uint8_t ret[8U]) {
  uint8_t ret0[8U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes) {
  int16_t uu____0 = (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____1 = (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____2 = (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____3 = (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____4 = (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____5 = (int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____6 = (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____7 = (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____8 = (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____9 = (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t,
                                                  uint8_t *, uint8_t);
  int16_t uu____10 = (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____11 = (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____12 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____13 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                   uint8_t *, uint8_t);
  int16_t uu____14 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                   uint8_t *, uint8_t);
  uint8_t coefficients = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      uu____0, uu____1, uu____2, uu____3, uu____4, uu____5, uu____6, uu____7,
      uu____8, uu____9, uu____10, uu____11, uu____12, uu____13, uu____14,
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *,
                                    uint8_t));
  uint8_t shift_lsbs_to_msbs = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  uint8_t coefficients_in_msb =
      libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(coefficients,
                                                        shift_lsbs_to_msbs);
  uint8_t coefficients_in_lsb =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
          (int32_t)4, coefficients_in_msb, uint8_t);
  uint8_t uu____15 = coefficients_in_lsb;
  return libcrux_intrinsics_avx2_extract_mm256_and_si256(
      uu____15, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                    ((int16_t)1 << 4U) - (int16_t)1));
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_4(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    uint8_t vector, uint8_t ret[10U]) {
  uint8_t serialized[32U] = {0U};
  uint8_t uu____0 = vector;
  uint8_t adjacent_2_combined =
      libcrux_intrinsics_avx2_extract_mm256_madd_epi16(
          uu____0,
          libcrux_intrinsics_avx2_extract_mm256_set_epi16(
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1,
              (int16_t)1 << 5U, (int16_t)1, (int16_t)1 << 5U, (int16_t)1));
  uint8_t uu____1 = adjacent_2_combined;
  uint8_t adjacent_4_combined =
      libcrux_intrinsics_avx2_extract_mm256_sllv_epi32(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi32(
                       (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22,
                       (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22));
  uint8_t adjacent_4_combined0 =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi64(
          (int32_t)22, adjacent_4_combined, uint8_t);
  uint8_t adjacent_8_combined =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(
          (int32_t)8, adjacent_4_combined0, uint8_t);
  uint8_t uu____2 = adjacent_8_combined;
  uint8_t adjacent_8_combined0 =
      libcrux_intrinsics_avx2_extract_mm256_sllv_epi32(
          uu____2, libcrux_intrinsics_avx2_extract_mm256_set_epi32(
                       (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12,
                       (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)12));
  uint8_t adjacent_8_combined1 =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi64(
          (int32_t)12, adjacent_8_combined0, uint8_t);
  uint8_t lower_8 = libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(
      adjacent_8_combined1);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)16U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      lower_8);
  uint8_t upper_8 = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined1, uint8_t);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)5U, .end = (size_t)21U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      upper_8);
  uint8_t ret0[10U];
  core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)10U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      Eurydice_slice, uint8_t[10U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_10size_t__core_array_TryFromSliceError(
      dst, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_5(
    uint8_t vector, uint8_t ret[10U]) {
  uint8_t ret0[10U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes) {
  uint8_t uu____0 =
      Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____1 =
      Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____2 =
      Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____3 =
      Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____4 =
      Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____5 =
      Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____6 =
      Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____7 =
      Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____8 =
      Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____9 =
      Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____10 =
      Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____11 =
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____12 =
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____13 =
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *, uint8_t);
  uint8_t uu____14 =
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *, uint8_t);
  uint8_t coefficients = libcrux_intrinsics_avx2_extract_mm_set_epi8(
      uu____0, uu____1, uu____2, uu____3, uu____4, uu____5, uu____6, uu____7,
      uu____8, uu____9, uu____10, uu____11, uu____12, uu____13, uu____14,
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *, uint8_t));
  uint8_t coefficients_loaded =
      libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(coefficients);
  uint8_t coefficients_loaded0 =
      libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
          (int32_t)1, coefficients_loaded, coefficients, uint8_t);
  uint8_t uu____15 = coefficients_loaded0;
  uint8_t coefficients0 = libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(
      uu____15,
      libcrux_intrinsics_avx2_extract_mm256_set_epi8(
          (int8_t)15, (int8_t)14, (int8_t)15, (int8_t)14, (int8_t)13,
          (int8_t)12, (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10,
          (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)9, (int8_t)8,
          (int8_t)7, (int8_t)6, (int8_t)7, (int8_t)6, (int8_t)5, (int8_t)4,
          (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)3, (int8_t)2,
          (int8_t)1, (int8_t)0, (int8_t)1, (int8_t)0));
  uint8_t uu____16 = coefficients0;
  uint8_t coefficients1 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      uu____16, libcrux_intrinsics_avx2_extract_mm256_set_epi16(
                    (int16_t)1 << 0U, (int16_t)1 << 5U, (int16_t)1 << 2U,
                    (int16_t)1 << 7U, (int16_t)1 << 4U, (int16_t)1 << 9U,
                    (int16_t)1 << 6U, (int16_t)1 << 11U, (int16_t)1 << 0U,
                    (int16_t)1 << 5U, (int16_t)1 << 2U, (int16_t)1 << 7U,
                    (int16_t)1 << 4U, (int16_t)1 << 9U, (int16_t)1 << 6U,
                    (int16_t)1 << 11U));
  return libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
      (int32_t)11, coefficients1, uint8_t);
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_5(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_5(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    uint8_t vector, uint8_t ret[20U]) {
  uint8_t serialized[32U] = {0U};
  uint8_t uu____0 = vector;
  uint8_t adjacent_2_combined =
      libcrux_intrinsics_avx2_extract_mm256_madd_epi16(
          uu____0,
          libcrux_intrinsics_avx2_extract_mm256_set_epi16(
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1,
              (int16_t)1 << 10U, (int16_t)1, (int16_t)1 << 10U, (int16_t)1));
  uint8_t uu____1 = adjacent_2_combined;
  uint8_t adjacent_4_combined =
      libcrux_intrinsics_avx2_extract_mm256_sllv_epi32(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi32(
                       (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12,
                       (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12));
  uint8_t adjacent_4_combined0 =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi64(
          (int32_t)12, adjacent_4_combined, uint8_t);
  uint8_t uu____2 = adjacent_4_combined0;
  uint8_t adjacent_8_combined =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(
          uu____2, libcrux_intrinsics_avx2_extract_mm256_set_epi8(
                       (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                       (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)11,
                       (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)4, (int8_t)3,
                       (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1, (int8_t)-1,
                       (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                       (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
                       (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  uint8_t lower_8 = libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(
      adjacent_8_combined);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)16U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      lower_8);
  uint8_t upper_8 = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, uint8_t);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)10U, .end = (size_t)26U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      upper_8);
  uint8_t ret0[20U];
  core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)20U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      Eurydice_slice, uint8_t[20U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_20size_t__core_array_TryFromSliceError(
      dst, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_10(
    uint8_t vector, uint8_t ret[20U]) {
  uint8_t ret0[20U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, ret0);
  memcpy(ret, ret0, (size_t)20U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes) {
  uint8_t shift_lsbs_to_msbs = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
      (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U);
  uint8_t lower_coefficients =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_slice_subslice(
          bytes,
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = (size_t)16U}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  uint8_t uu____0 = lower_coefficients;
  uint8_t lower_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm_set_epi8(
          9U, 8U, 8U, 7U, 7U, 6U, 6U, 5U, 4U, 3U, 3U, 2U, 2U, 1U, 1U, 0U));
  uint8_t upper_coefficients =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_slice_subslice(
          bytes,
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)4U,
                                                  .end = (size_t)20U}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  uint8_t uu____1 = upper_coefficients;
  uint8_t upper_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      uu____1, libcrux_intrinsics_avx2_extract_mm_set_epi8(
                   15U, 14U, 14U, 13U, 13U, 12U, 12U, 11U, 10U, 9U, 9U, 8U, 8U,
                   7U, 7U, 6U));
  uint8_t coefficients = libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(
      lower_coefficients0);
  uint8_t coefficients0 =
      libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
          (int32_t)1, coefficients, upper_coefficients0, uint8_t);
  uint8_t coefficients1 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      coefficients0, shift_lsbs_to_msbs);
  uint8_t coefficients2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
      (int32_t)6, coefficients1, uint8_t);
  uint8_t uu____2 = coefficients2;
  uint8_t coefficients3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      uu____2, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                   ((int16_t)1 << 10U) - (int16_t)1));
  return coefficients3;
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_10(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    uint8_t vector, uint8_t ret[22U]) {
  int16_t array[16U] = {0U};
  libcrux_intrinsics_avx2_extract_mm256_storeu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice),
      vector);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__portable__vector_type__PortableVector___from_i16_array(
          Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__portable__vector_type__PortableVector___serialize_11(
      input, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_11(
    uint8_t vector, uint8_t ret[22U]) {
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__portable__vector_type__PortableVector___deserialize_11(
          bytes);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__portable__vector_type__PortableVector___to_i16_array(
      output, array);
  return libcrux_intrinsics_avx2_extract_mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, array, int16_t, Eurydice_slice));
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_11(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_11(bytes);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    uint8_t vector, uint8_t ret[24U]) {
  uint8_t serialized[32U] = {0U};
  uint8_t uu____0 = vector;
  uint8_t adjacent_2_combined =
      libcrux_intrinsics_avx2_extract_mm256_madd_epi16(
          uu____0,
          libcrux_intrinsics_avx2_extract_mm256_set_epi16(
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1,
              (int16_t)1 << 12U, (int16_t)1, (int16_t)1 << 12U, (int16_t)1));
  uint8_t uu____1 = adjacent_2_combined;
  uint8_t adjacent_4_combined =
      libcrux_intrinsics_avx2_extract_mm256_sllv_epi32(
          uu____1, libcrux_intrinsics_avx2_extract_mm256_set_epi32(
                       (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8,
                       (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8));
  uint8_t adjacent_4_combined0 =
      libcrux_intrinsics_avx2_extract_mm256_srli_epi64(
          (int32_t)8, adjacent_4_combined, uint8_t);
  uint8_t uu____2 = adjacent_4_combined0;
  uint8_t adjacent_8_combined =
      libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(
          uu____2, libcrux_intrinsics_avx2_extract_mm256_set_epi8(
                       (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
                       (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)10,
                       (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4, (int8_t)3,
                       (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1, (int8_t)-1,
                       (int8_t)-1, (int8_t)-1, (int8_t)13, (int8_t)12,
                       (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)5,
                       (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  uint8_t lower_8 = libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(
      adjacent_8_combined);
  uint8_t upper_8 = libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, uint8_t);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)16U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      lower_8);
  libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)12U, .end = (size_t)28U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      upper_8);
  uint8_t ret0[24U];
  core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice((size_t)32U, serialized,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)24U}),
                                 uint8_t, core_ops_range_Range__size_t,
                                 Eurydice_slice),
      Eurydice_slice, uint8_t[24U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_24size_t__core_array_TryFromSliceError(
      dst, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_12(
    uint8_t vector, uint8_t ret[24U]) {
  uint8_t ret0[24U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, ret0);
  memcpy(ret, ret0, (size_t)24U * sizeof(uint8_t));
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes) {
  uint8_t shift_lsbs_to_msbs = libcrux_intrinsics_avx2_extract_mm256_set_epi16(
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
      (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U);
  uint8_t lower_coefficients =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_slice_subslice(
          bytes,
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = (size_t)16U}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  uint8_t uu____0 = lower_coefficients;
  uint8_t lower_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      uu____0,
      libcrux_intrinsics_avx2_extract_mm_set_epi8(
          11U, 10U, 10U, 9U, 8U, 7U, 7U, 6U, 5U, 4U, 4U, 3U, 2U, 1U, 1U, 0U));
  uint8_t upper_coefficients =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_slice_subslice(
          bytes,
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)8U,
                                                  .end = (size_t)24U}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  uint8_t uu____1 = upper_coefficients;
  uint8_t upper_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      uu____1, libcrux_intrinsics_avx2_extract_mm_set_epi8(
                   15U, 14U, 14U, 13U, 12U, 11U, 11U, 10U, 9U, 8U, 8U, 7U, 6U,
                   5U, 5U, 4U));
  uint8_t coefficients = libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(
      lower_coefficients0);
  uint8_t coefficients0 =
      libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
          (int32_t)1, coefficients, upper_coefficients0, uint8_t);
  uint8_t coefficients1 = libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(
      coefficients0, shift_lsbs_to_msbs);
  uint8_t coefficients2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi16(
      (int32_t)4, coefficients1, uint8_t);
  uint8_t uu____2 = coefficients2;
  uint8_t coefficients3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      uu____2, libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
                   ((int16_t)1 << 12U) - (int16_t)1));
  return coefficients3;
}

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_12(
    Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t potential_coefficients =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_12(input);
  uint8_t compare_with_field_modulus =
      libcrux_intrinsics_avx2_extract_mm256_cmpgt_epi16(field_modulus,
                                                        potential_coefficients);
  uint8_t good[2U];
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(compare_with_field_modulus,
                                                   good);
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[0U]],
         (size_t)16U * sizeof(uint8_t));
  uint8_t lower_shuffles0 =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_array_to_slice(
          (size_t)16U, lower_shuffles, uint8_t, Eurydice_slice));
  uint8_t lower_coefficients =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(
          potential_coefficients);
  uint8_t lower_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_extract_mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8_6__count_ones(good[0U]);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[1U]],
         (size_t)16U * sizeof(uint8_t));
  uint8_t upper_shuffles0 =
      libcrux_intrinsics_avx2_extract_mm_loadu_si128(Eurydice_array_to_slice(
          (size_t)16U, upper_shuffles, uint8_t, Eurydice_slice));
  uint8_t upper_coefficients =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
          (int32_t)1, potential_coefficients, uint8_t);
  uint8_t upper_coefficients0 = libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_extract_mm_storeu_si128(
      Eurydice_slice_subslice(
          output,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = sampled_count, .end = sampled_count + (size_t)8U}),
          int16_t, core_ops_range_Range__size_t, Eurydice_slice),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8_6__count_ones(good[1U]);
}

size_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
    Eurydice_slice input, Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

inline uint8_t
libcrux_ml_kem_vector_avx2___core__clone__Clone_for_libcrux_ml_kem__vector__avx2__SIMD256Vector__1__clone(
    uint8_t *self) {
  return self[0U];
}

static libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      lit;
  lit.coefficients[0U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[1U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[2U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[3U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[4U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[5U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[6U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[7U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[8U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[9U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[10U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[11U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[12U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[13U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[14U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  lit.coefficients[15U] =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  return lit;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t coefficient =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_12(
            bytes);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___cond_subtract_3329(
            coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1184size_t_3size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE uint8_t shift_right___15int32_t(uint8_t vector) {
  return libcrux_intrinsics_avx2_extract_mm256_srai_epi16((int32_t)15, vector,
                                                          uint8_t);
}

static uint8_t shift_right___15int32_t0(uint8_t vector) {
  return shift_right___15int32_t(vector);
}

static uint8_t
to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    uint8_t a) {
  uint8_t t = shift_right___15int32_t0(a);
  uint8_t fm =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___bitwise_and_with_constant(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
      a, &fm);
}

static KRML_MUSTINLINE void
serialize_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
    uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient =
        to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_12(
        coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)384U, serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = (size_t)24U * i0, .end = (size_t)24U * i0 + (size_t)24U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)24U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, serialized, (size_t)384U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *key,
    uint8_t ret[1152U]) {
  uint8_t out[1152U] = {0U};
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)3U, key,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)1152U, out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = (i0 + (size_t)1U) *
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)1152U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t_1184size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice(
      (size_t)1184U, public_key_serialized,
      (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                              .end = (size_t)1152U}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[1152U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t(
      t_as_ntt, ret0);
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

bool libcrux_ml_kem_ind_cca_validate_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t_1184size_t(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[3U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1184size_t_3size_t(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t_1184size_t(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

typedef struct
    __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      snd;
} __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t__;

static KRML_MUSTINLINE void G___3size_t(Eurydice_slice input,
                                        uint8_t ret[64U]) {
  uint8_t ret0[64U];
  libcrux_ml_kem_hash_functions_avx2_G(input, ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___3size_t(uint8_t input[3U][34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice));
  return state;
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___3size_t0(uint8_t input[3U][34U]) {
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb___3size_t(uu____0);
}

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___3size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___3size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][504U]) {
  uint8_t ret0[3U][504U];
  shake128_squeeze_three_blocks___3size_t(self, ret0);
  memcpy(ret, ret0, (size_t)3U * sizeof(uint8_t[504U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_504size_t(
    uint8_t randomness[3U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)504U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static KRML_MUSTINLINE void shake128_squeeze_block___3size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_block___3size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[3U][168U]) {
  uint8_t ret0[3U][168U];
  shake128_squeeze_block___3size_t(self, ret0);
  memcpy(ret, ret0, (size_t)3U * sizeof(uint8_t[168U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_168size_t(
    uint8_t randomness[3U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)168U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___from_i16_array(
            Eurydice_slice_subslice(
                a,
                (CLITERAL(core_ops_range_Range__size_t){
                    .start = i0 * (size_t)16U,
                    .end = (i0 + (size_t)1U) * (size_t)16U}),
                int16_t, core_ops_range_Range__size_t, Eurydice_slice));
    result.coefficients[i0] = uu____0;
  }
  return result;
}

static libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t0(
    int16_t s[272U]) {
  return from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      Eurydice_array_to_subslice((size_t)272U, s,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)256U}),
                                 int16_t, core_ops_range_Range__size_t,
                                 Eurydice_slice));
}

static KRML_MUSTINLINE void
sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb___3size_t0(uu____0);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_three_blocks___3size_t0(&xof_state, randomness0);
  uint8_t uu____1[3U][504U];
  memcpy(uu____1, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done =
      sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_504size_t(
          uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      shake128_squeeze_block___3size_t0(&xof_state, randomness);
      uint8_t uu____2[3U][168U];
      memcpy(uu____2, randomness, (size_t)3U * sizeof(uint8_t[168U]));
      done =
          sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_168size_t(
              uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[3U][272U];
  memcpy(uu____3, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      ret0[i] =
          closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t0(
              uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void
sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[3U][3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
          A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          sampled[3U];
      sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
          uu____1, sampled);
      for (
          size_t i = (size_t)0U;
          i <
          core_slice___Slice_T___len(
              Eurydice_array_to_slice(
                  (size_t)3U, sampled,
                  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                  Eurydice_slice),
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              size_t);
          i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(
      ret, A_transpose,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
}

typedef struct
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      fst[3U];
  uint8_t snd;
} __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t;

static KRML_MUSTINLINE void PRFxN___3size_t_128size_t(uint8_t (*input)[33U],
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

static KRML_MUSTINLINE void PRFxN___3size_t_128size_t0(uint8_t (*input)[33U],
                                                       uint8_t ret[3U][128U]) {
  uint8_t ret0[3U][128U];
  PRFxN___3size_t_128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)3U * sizeof(uint8_t[128U]));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    sample_from_binomial_distribution_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 <
       core_slice___Slice_T___len(randomness, uint8_t, size_t) / (size_t)4U;
       i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice(
        randomness,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = chunk_number * (size_t)4U,
            .end = chunk_number * (size_t)4U + (size_t)4U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint32_t uu____0 = (uint32_t)Eurydice_slice_index(
        byte_chunk, (size_t)0U, uint8_t, uint8_t *, uint8_t);
    uint32_t uu____1 =
        uu____0 | (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U,
                                                 uint8_t, uint8_t *, uint8_t)
                      << 8U;
    uint32_t uu____2 =
        uu____1 | (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U,
                                                 uint8_t, uint8_t *, uint8_t)
                      << 16U;
    uint32_t random_bits_as_u32 =
        uu____2 | (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U,
                                                 uint8_t, uint8_t *, uint8_t)
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
  return from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t,
                              Eurydice_slice));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    sample_from_binomial_distribution_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 <
       core_slice___Slice_T___len(randomness, uint8_t, size_t) / (size_t)3U;
       i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice(
        randomness,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = chunk_number * (size_t)3U,
            .end = chunk_number * (size_t)3U + (size_t)3U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint32_t uu____0 = (uint32_t)Eurydice_slice_index(
        byte_chunk, (size_t)0U, uint8_t, uint8_t *, uint8_t);
    uint32_t uu____1 =
        uu____0 | (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U,
                                                 uint8_t, uint8_t *, uint8_t)
                      << 8U;
    uint32_t random_bits_as_u24 =
        uu____1 | (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U,
                                                 uint8_t, uint8_t *, uint8_t)
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
  return from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t,
                              Eurydice_slice));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
        Eurydice_slice randomness) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      sample_from_binomial_distribution_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          randomness);
  return uu____0;
}

static KRML_MUSTINLINE void
ntt_at_layer_7__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    uint8_t t =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___multiply_by_constant(
            re->coefficients[j + step], (int16_t)-1600);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
            re->coefficients[j], &t);
    re->coefficients[j + step] = uu____0;
    uint8_t uu____1 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            re->coefficients[j], &t);
    re->coefficients[j] = uu____1;
  }
}

typedef struct
    __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector_s {
  uint8_t fst;
  uint8_t snd;
} __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector;

static uint8_t montgomery_multiply_fe__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    uint8_t v, int16_t fer) {
  return libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
      v, fer);
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector
    ntt_layer_int_vec_step__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        uint8_t a, uint8_t b, int16_t zeta_r) {
  uint8_t t = montgomery_multiply_fe__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      b, zeta_r);
  b = libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
      a, &t);
  a = libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
      a, &t);
  return (CLITERAL(
      __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector){
      .fst = a, .snd = b});
}

static KRML_MUSTINLINE void
ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
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
      __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____0 =
              ntt_layer_int_vec_step__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                  re->coefficients[j], re->coefficients[j + step_vec],
                  libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R
                      [zeta_i[0U]]);
      uint8_t x = uu____0.fst;
      uint8_t y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

static KRML_MUSTINLINE void
ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_3_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      re->coefficients[round] = uu____0;);
}

static KRML_MUSTINLINE void
ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_2_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                                 (size_t)1U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

static KRML_MUSTINLINE void
ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_1_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                                 (size_t)1U],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                                 (size_t)2U],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                                 (size_t)3U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

static KRML_MUSTINLINE void
poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
            self->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

static KRML_MUSTINLINE void
ntt_binomially_sampled_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  ntt_at_layer_7__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)6U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)5U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)4U);
  ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
    sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re_as_ntt[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      re_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___3size_t_128size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
                  Eurydice_array_to_slice((size_t)128U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          &re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[3U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *self,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      out = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_multiply(
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
    out.coefficients[i0] = uu____0;
  }
  return out;
}

static KRML_MUSTINLINE void
add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)16U, self->coefficients, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t);
       i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            self->coefficients[i0], &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

static uint8_t to_standard_domain__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    uint8_t v) {
  return libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

static KRML_MUSTINLINE void
add_standard_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    uint8_t coefficient_normal_form =
        to_standard_domain__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            self->coefficients[j]);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
            libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
                coefficient_normal_form, &error->coefficients[j]));
    self->coefficients[j] = uu____0;
  }
}

static KRML_MUSTINLINE void
compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)3U, matrix_A,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [3U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = matrix_A[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)3U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *matrix_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              matrix_element, &s_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
          &result[i1], &product);
    }
    add_standard_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t__
generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G___3size_t(key_generation_seed, hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          (size_t)32U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[3U][3U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed_for_A0, ret);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
      ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(seed_for_secret_and_error,
                                                    prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
      uu____2 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
              uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[3U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
          uu____3, domain_separator)
          .fst,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[3U];
  compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
      A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____4[3U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[3U][3U];
  memcpy(
      uu____5, A_transpose,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(
      pk.A, uu____5,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____7[3U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  return (CLITERAL(
      __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t__){
      .fst = sk, .snd = pk});
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_2400size_t_1184size_t_1152size_t_2size_t_128size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static inline libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
clone__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      lit;
  uint8_t ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret, uint8_t, void *);
  memcpy(lit.coefficients, ret, (size_t)16U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void H___3size_t(Eurydice_slice input,
                                        uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_avx2_H(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_2400size_t_1184size_t_1152size_t_2size_t_128size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
              ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[3U][3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_2400size_t_1184size_t_1152size_t_2size_t_128size_t(
          A[i]););
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              uu____1 = clone__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                  &ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[3U][3U];
  memcpy(
      uu____2, A,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  memcpy(
      ind_cpa_public_key.A, uu____2,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  uint8_t pk_serialized[1184U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t_1184size_t(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H___3size_t(Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t,
                                      Eurydice_slice),
              public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      uu____3 = ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      uu____6 = ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

static libcrux_ml_kem_utils_extraction_helper_Keypair768
generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_1184size_t_1152size_t_2size_t_128size_t(
    Eurydice_slice key_generation_seed) {
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___3size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
              key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      pk = uu____0.snd;
  uint8_t public_key_serialized[1184U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t_1184size_t(
      pk.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t,
                              Eurydice_slice),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1152size_t(
      sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[1152U];
  memcpy(uu____1, secret_key_serialized, (size_t)1152U * sizeof(uint8_t));
  uint8_t uu____2[1184U];
  memcpy(uu____2, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair768 lit;
  memcpy(lit.fst, uu____1, (size_t)1152U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2400size_t(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)2400U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____1,
              .end = uu____2 +
                     core_slice___Slice_T___len(private_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)2400U, uu____3,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____4,
              .end = uu____5 +
                     core_slice___Slice_T___len(public_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice(
      (size_t)2400U, out,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = pointer,
          .end = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[32U];
  H___3size_t(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)2400U, uu____7,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____8,
              .end = uu____9 + core_slice___Slice_T___len(
                                   implicit_rejection_value, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
  memcpy(ret, out, (size_t)2400U * sizeof(uint8_t));
}

libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_2400size_t_1184size_t_1152size_t_2size_t_128size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1152size_t_1184size_t_1152size_t_2size_t_128size_t(
          ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2400size_t(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[2400U];
  memcpy(uu____1, secret_key_serialized, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____2400size_t private_key =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___2400size_t(
          uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey____2400size_t uu____2 = private_key;
  uint8_t uu____3[1184U];
  memcpy(uu____3, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___2400size_t_1184size_t(
      uu____2,
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1184size_t(
          uu____3));
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
    sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_128size_t_2size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      error_1[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___3size_t_128size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
                  Eurydice_array_to_slice((size_t)128U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[3U];
  memcpy(
      uu____2, error_1,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE void PRF___128size_t(Eurydice_slice input,
                                            uint8_t ret[128U]) {
  uint8_t digest[128U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)128U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void PRF___3size_t_128size_t(Eurydice_slice input,
                                                    uint8_t ret[128U]) {
  uint8_t ret0[128U];
  PRF___128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)128U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
invert_ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_1_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)1U],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)2U],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)3U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

static KRML_MUSTINLINE void
invert_ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_2_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)1U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

static KRML_MUSTINLINE void
invert_ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      uint8_t uu____0 =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_3_step(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      re->coefficients[round] = uu____0;);
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector
    inv_ntt_layer_int_vec_step_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        uint8_t a, uint8_t b, int16_t zeta_r) {
  uint8_t a_minus_b =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
          b, &a);
  a = libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
          a, &b));
  b = montgomery_multiply_fe__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      a_minus_b, zeta_r);
  return (CLITERAL(
      __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector){
      .fst = a, .snd = b});
}

static KRML_MUSTINLINE void
invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    size_t *zeta_i,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
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
      __libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____0 =
              inv_ntt_layer_int_vec_step_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                  re->coefficients[j], re->coefficients[j + step_vec],
                  libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R
                      [zeta_i[0U]]);
      uint8_t x = uu____0.fst;
      uint8_t y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

static KRML_MUSTINLINE void
invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)7U);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE void
add_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    uint8_t coefficient_normal_form =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
            self->coefficients[j], (int16_t)1441);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
            libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
                coefficient_normal_form, &error->coefficients[j]));
    self->coefficients[j] = uu____0;
  }
}

static KRML_MUSTINLINE void
compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)3U, a_as_ntt,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [3U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = a_as_ntt[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)3U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              a_element, &r_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
          &result[i1], &product);
    }
    invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
        &result[i1]);
    add_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(&result[i1],
                                                               &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static uint8_t decompress_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    uint8_t v) {
  uint8_t uu____0 =
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO();
  return libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___bitwise_and_with_constant(
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
          uu____0, &v),
      (int16_t)1665);
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      uint8_t coefficient_compressed =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_1(
              Eurydice_array_to_subslice(
                  (size_t)32U, serialized,
                  (CLITERAL(core_ops_range_Range__size_t){
                      .start = (size_t)2U * i0,
                      .end = (size_t)2U * i0 + (size_t)2U}),
                  uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
      uint8_t uu____0 = decompress_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          coefficient_compressed);
      re.coefficients[i0] = uu____0;);
  return re;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    add_message_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *self,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *message,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient_normal_form =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
            result.coefficients[i0], (int16_t)1441);
    uint8_t tmp =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            self->coefficients[i0], &message->coefficients[i0]);
    uint8_t tmp0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            coefficient_normal_form, &tmp);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
            tmp0);
    result.coefficients[i0] = uu____0;
  }
  return result;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *t_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *r_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *error_2,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &t_as_ntt[i0], &r_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
      &result);
  result = add_message_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      error_2, message, result);
  return result;
}

static KRML_MUSTINLINE uint8_t
compress_ciphertext_coefficient___10int32_t(uint8_t vector) {
  uint8_t field_modulus_halved =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  uint8_t compression_factor =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)10321340);
  uint8_t coefficient_bits_mask =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)10) - (int32_t)1);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t compressed_low = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)10, coefficients_low0, uint8_t);
  uint8_t compressed_low0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  uint8_t compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  uint8_t compressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_low1, uint8_t);
  uint8_t compressed_low3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t compressed_high = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)10, coefficients_high0, uint8_t);
  uint8_t compressed_high0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  uint8_t compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  uint8_t compressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_high1, uint8_t);
  uint8_t compressed_high3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t compress___10int32_t(uint8_t vector) {
  return compress_ciphertext_coefficient___10int32_t(vector);
}

static KRML_MUSTINLINE void
compress_then_serialize_10__libcrux_ml_kem_vector_avx2_SIMD256Vector_320size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
    uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient = compress___10int32_t(
        to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_10(
        coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)320U, serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = (size_t)20U * i0, .end = (size_t)20U * i0 + (size_t)20U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)20U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

static KRML_MUSTINLINE uint8_t
compress_ciphertext_coefficient___11int32_t(uint8_t vector) {
  uint8_t field_modulus_halved =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  uint8_t compression_factor =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)10321340);
  uint8_t coefficient_bits_mask =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)11) - (int32_t)1);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t compressed_low = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)11, coefficients_low0, uint8_t);
  uint8_t compressed_low0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  uint8_t compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  uint8_t compressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_low1, uint8_t);
  uint8_t compressed_low3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t compressed_high = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)11, coefficients_high0, uint8_t);
  uint8_t compressed_high0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  uint8_t compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  uint8_t compressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_high1, uint8_t);
  uint8_t compressed_high3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t compress___11int32_t(uint8_t vector) {
  return compress_ciphertext_coefficient___11int32_t(vector);
}

static KRML_MUSTINLINE void
compress_then_serialize_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t_320size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
    uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10__libcrux_ml_kem_vector_avx2_SIMD256Vector_320size_t(
      re, uu____0);
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

static void
compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_960size_t_10size_t_320size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        input[3U],
    Eurydice_slice out) {
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)3U, input,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * ((size_t)960U / (size_t)3U),
            .end = (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U)}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t_320size_t(
        &re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE uint8_t
compress_ciphertext_coefficient___4int32_t(uint8_t vector) {
  uint8_t field_modulus_halved =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  uint8_t compression_factor =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)10321340);
  uint8_t coefficient_bits_mask =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)4) - (int32_t)1);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t compressed_low = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)4, coefficients_low0, uint8_t);
  uint8_t compressed_low0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  uint8_t compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  uint8_t compressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_low1, uint8_t);
  uint8_t compressed_low3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t compressed_high = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)4, coefficients_high0, uint8_t);
  uint8_t compressed_high0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  uint8_t compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  uint8_t compressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_high1, uint8_t);
  uint8_t compressed_high3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t compress___4int32_t(uint8_t vector) {
  return compress_ciphertext_coefficient___4int32_t(vector);
}

static KRML_MUSTINLINE void
compress_then_serialize_4__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient = compress___4int32_t(
        to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_4(
        coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE uint8_t
compress_ciphertext_coefficient___5int32_t(uint8_t vector) {
  uint8_t field_modulus_halved =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
          (int32_t)2);
  uint8_t compression_factor =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)10321340);
  uint8_t coefficient_bits_mask =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          ((int32_t)1 << (uint32_t)(int32_t)5) - (int32_t)1);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t compressed_low = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)5, coefficients_low0, uint8_t);
  uint8_t compressed_low0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  uint8_t compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  uint8_t compressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_low1, uint8_t);
  uint8_t compressed_low3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t compressed_high = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)5, coefficients_high0, uint8_t);
  uint8_t compressed_high0 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  uint8_t compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  uint8_t compressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)3, compressed_high1, uint8_t);
  uint8_t compressed_high3 = libcrux_intrinsics_avx2_extract_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t compress___5int32_t(uint8_t vector) {
  return compress_ciphertext_coefficient___5int32_t(vector);
}

static KRML_MUSTINLINE void
compress_then_serialize_5__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficients = compress___5int32_t(
        to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_5(
        coefficients, bytes);
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = (size_t)10U * i0, .end = (size_t)10U * i0 + (size_t)10U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)10U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
compress_then_serialize_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_128size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re,
    Eurydice_slice out) {
  compress_then_serialize_4__libcrux_ml_kem_vector_avx2_SIMD256Vector(re, out);
}

static void
encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
        *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
      uu____1 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2size_t_128size_t(
              uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t__uint8_t
      uu____3 =
          sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_128size_t_2size_t(
              uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF___3size_t_128size_t(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_2 =
          sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
              Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t,
                                      Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u[3U];
  compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
      public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message_as_ring_element =
          deserialize_then_decompress_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
          public_key->t_as_ntt, r_as_ntt, &error_2, &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_960size_t_10size_t_320size_t(
      uu____5, Eurydice_array_to_subslice(
                   (size_t)1088U, ciphertext,
                   (CLITERAL(core_ops_range_Range__size_t){
                       .start = (size_t)0U, .end = (size_t)960U}),
                   uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____6 = v;
  compress_then_serialize_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_128size_t(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1184size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
        *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___3size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      *uu____2 = &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1088size_t(
          uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1152size_t_3size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
    Eurydice_slice public_key, uint8_t message[32U], Eurydice_slice randomness,
    uint8_t ret[1088U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[3U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1152size_t_3size_t(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[3U][3U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed, ret0);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
      ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[3U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____1[3U][3U];
  memcpy(
      uu____1, A,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(
      public_key_unpacked.A, uu____1,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [3U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      *uu____3 = &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1088U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
      uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1088U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t(
    Eurydice_slice shared_secret, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_3size_t_1088size_t_1184size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H___3size_t(
      Eurydice_array_to_slice(
          (size_t)1184U,
          libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1184size_t(
              public_key),
          uint8_t, Eurydice_slice),
      ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G___3size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U,
      libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1184size_t(
          public_key),
      uint8_t, Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1088size_t(
          uu____4);
  uint8_t shared_secret_array[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t(
      shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE uint8_t
decompress_ciphertext_coefficient___10int32_t(uint8_t vector) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          (int32_t)1 << (uint32_t)(int32_t)10);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t decompressed_low = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  uint8_t decompressed_low0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_low, uint8_t);
  uint8_t decompressed_low1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  uint8_t decompressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)10, decompressed_low1, uint8_t);
  uint8_t decompressed_low3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, uint8_t);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t decompressed_high = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  uint8_t decompressed_high0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_high, uint8_t);
  uint8_t decompressed_high1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  uint8_t decompressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)10, decompressed_high1, uint8_t);
  uint8_t decompressed_high3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, uint8_t);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t decompress_ciphertext_coefficient___10int32_t0(uint8_t vector) {
  return decompress_ciphertext_coefficient___10int32_t(vector);
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_10__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)20U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)20U, .end = i0 * (size_t)20U + (size_t)20U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t coefficient =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_10(
            bytes);
    uint8_t uu____0 =
        decompress_ciphertext_coefficient___10int32_t0(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

static KRML_MUSTINLINE uint8_t
decompress_ciphertext_coefficient___11int32_t(uint8_t vector) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
          (int32_t)1 << (uint32_t)(int32_t)11);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t decompressed_low = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  uint8_t decompressed_low0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_low, uint8_t);
  uint8_t decompressed_low1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  uint8_t decompressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)11, decompressed_low1, uint8_t);
  uint8_t decompressed_low3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, uint8_t);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t decompressed_high = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  uint8_t decompressed_high0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_high, uint8_t);
  uint8_t decompressed_high1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  uint8_t decompressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)11, decompressed_high1, uint8_t);
  uint8_t decompressed_high3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, uint8_t);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t decompress_ciphertext_coefficient___11int32_t0(uint8_t vector) {
  return decompress_ciphertext_coefficient___11int32_t(vector);
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_11__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)22U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)22U, .end = i0 * (size_t)22U + (size_t)22U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t coefficient =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_11(
            bytes);
    uint8_t uu____0 =
        decompress_ciphertext_coefficient___11int32_t0(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      deserialize_then_decompress_10__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          serialized);
  return uu____0;
}

static KRML_MUSTINLINE void
ntt_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)7U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)6U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)5U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)4U);
  ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE void
deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_10size_t(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      u_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice(
        (size_t)1088U, ciphertext,
        (CLITERAL(core_ops_range_Range__size_t){
            .start =
                i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                      (size_t)10U / (size_t)8U),
            .end = i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                         (size_t)10U / (size_t)8U) +
                   LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                       (size_t)10U / (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_then_decompress_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
                u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
        &u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE uint8_t
decompress_ciphertext_coefficient___4int32_t(uint8_t vector) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)1
                                                       << (uint32_t)(int32_t)4);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t decompressed_low = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  uint8_t decompressed_low0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_low, uint8_t);
  uint8_t decompressed_low1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  uint8_t decompressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)4, decompressed_low1, uint8_t);
  uint8_t decompressed_low3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, uint8_t);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t decompressed_high = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  uint8_t decompressed_high0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_high, uint8_t);
  uint8_t decompressed_high1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  uint8_t decompressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)4, decompressed_high1, uint8_t);
  uint8_t decompressed_high3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, uint8_t);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t decompress_ciphertext_coefficient___4int32_t0(uint8_t vector) {
  return decompress_ciphertext_coefficient___4int32_t(vector);
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_4__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)8U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t coefficient =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_4(
            bytes);
    uint8_t uu____0 =
        decompress_ciphertext_coefficient___4int32_t0(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

static KRML_MUSTINLINE uint8_t
decompress_ciphertext_coefficient___5int32_t(uint8_t vector) {
  uint8_t field_modulus = libcrux_intrinsics_avx2_extract_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t two_pow_coefficient_bits =
      libcrux_intrinsics_avx2_extract_mm256_set1_epi32((int32_t)1
                                                       << (uint32_t)(int32_t)5);
  uint8_t coefficients_low =
      libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(vector);
  uint8_t coefficients_low0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_low);
  uint8_t decompressed_low = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  uint8_t decompressed_low0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_low, uint8_t);
  uint8_t decompressed_low1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  uint8_t decompressed_low2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)5, decompressed_low1, uint8_t);
  uint8_t decompressed_low3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, uint8_t);
  uint8_t coefficients_high =
      libcrux_intrinsics_avx2_extract_mm256_extracti128_si256((int32_t)1,
                                                              vector, uint8_t);
  uint8_t coefficients_high0 =
      libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(coefficients_high);
  uint8_t decompressed_high = libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  uint8_t decompressed_high0 = libcrux_intrinsics_avx2_extract_mm256_slli_epi32(
      (int32_t)1, decompressed_high, uint8_t);
  uint8_t decompressed_high1 = libcrux_intrinsics_avx2_extract_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  uint8_t decompressed_high2 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)5, decompressed_high1, uint8_t);
  uint8_t decompressed_high3 = libcrux_intrinsics_avx2_extract_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, uint8_t);
  uint8_t compressed = libcrux_intrinsics_avx2_extract_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  return libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
      (int32_t)216, compressed, uint8_t);
}

static uint8_t decompress_ciphertext_coefficient___5int32_t0(uint8_t vector) {
  return decompress_ciphertext_coefficient___5int32_t(vector);
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_5__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)10U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)10U, .end = i0 * (size_t)10U + (size_t)10U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_5(
            bytes);
    re.coefficients[i0] = uu____0;
    uint8_t uu____1 =
        decompress_ciphertext_coefficient___5int32_t0(re.coefficients[i0]);
    re.coefficients[i0] = uu____1;
  }
  return re;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      deserialize_then_decompress_4__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          serialized);
  return uu____0;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    subtract_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *self,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient_normal_form =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
            b.coefficients[i0], (int16_t)1441);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
            libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
                self->coefficients[i0], &coefficient_normal_form));
    b.coefficients[i0] = uu____0;
  }
  return b;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *v,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *secret_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &secret_as_ntt[i0], &u_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
      &result);
  result = subtract_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(v, result);
  return result;
}

static KRML_MUSTINLINE void
compress_then_serialize_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re,
    uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      uint8_t coefficient =
          to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              re.coefficients[i0]);
      uint8_t coefficient_compressed =
          libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___compress_1(
              coefficient);
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_1(
          coefficient_compressed, bytes);
      Eurydice_slice uu____0 = Eurydice_array_to_subslice(
          (size_t)32U, serialized,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)2U * i0, .end = (size_t)2U * i0 + (size_t)2U}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____0,
          Eurydice_array_to_slice((size_t)2U, bytes, uint8_t, Eurydice_slice),
          uint8_t, void *););
  memcpy(ret, serialized, (size_t)32U * sizeof(uint8_t));
}

static void
decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_960size_t_10size_t_4size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
        *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[3U];
  deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_10size_t(
      ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = deserialize_then_decompress_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message =
          compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
              &v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void PRF___32size_t(Eurydice_slice input,
                                           uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void PRF___3size_t_32size_t(Eurydice_slice input,
                                                   uint8_t ret[32U]) {
  uint8_t ret0[32U];
  PRF___32size_t(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_2400size_t_1152size_t_1184size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t_1120size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
        *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_960size_t_10size_t_4size_t(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___3size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array___1120size_t(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF___3size_t_32size_t(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      *uu____3 = &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
      uu____3, uu____4, pseudorandomness, expected_ciphertext);
  Eurydice_slice uu____5 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
          ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          uu____5, Eurydice_array_to_slice((size_t)1088U, expected_ciphertext,
                                           uint8_t, Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_to_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice(
        serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_12(
            bytes);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

static KRML_MUSTINLINE void
deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[3U];
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U,
      secret_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice(
        secret_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_960size_t_10size_t_4size_t(
    Eurydice_slice secret_key, uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[3U];
  deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
      secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[3U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)3U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t ret0[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_960size_t_10size_t_4size_t(
      &secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_3size_t_2400size_t_1152size_t_1184size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t_1120size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t,
                                  Eurydice_slice),
          (size_t)1152U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          secret_key0, (size_t)1184U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____2 =
      core_slice___Slice_T___split_at(
          secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t_1088size_t_960size_t_10size_t_4size_t(
      ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G___3size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____3 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array___1120size_t(implicit_rejection_value,
                                                      to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF___3size_t_32size_t(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t_1152size_t_960size_t_128size_t_10size_t_4size_t_320size_t_2size_t_128size_t_2size_t_128size_t(
      uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_3size_t_1088size_t(
      shared_secret0, shared_secret);
  Eurydice_slice uu____7 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
          ciphertext);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____7,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1568size_t_4size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void
serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *key,
    uint8_t ret[1536U]) {
  uint8_t out[1536U] = {0U};
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)4U, key,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)1536U, out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = (i0 + (size_t)1U) *
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)1536U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t_1568size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice(
      (size_t)1568U, public_key_serialized,
      (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                              .end = (size_t)1536U}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[1536U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t(
      t_as_ntt, ret0);
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

bool libcrux_ml_kem_ind_cca_validate_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t_1568size_t(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[4U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1568size_t_4size_t(
      Eurydice_array_to_subslice_to((size_t)1568U, public_key, (size_t)1536U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t_1568size_t(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1568U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

typedef struct
    __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      snd;
} __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t__;

static KRML_MUSTINLINE void G___4size_t(Eurydice_slice input,
                                        uint8_t ret[64U]) {
  uint8_t ret0[64U];
  libcrux_ml_kem_hash_functions_avx2_G(input, ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___4size_t(uint8_t input[4U][34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[3U], uint8_t, Eurydice_slice));
  return state;
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___4size_t0(uint8_t input[4U][34U]) {
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb___4size_t(uu____0);
}

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___4size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___4size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][504U]) {
  uint8_t ret0[4U][504U];
  shake128_squeeze_three_blocks___4size_t(self, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(uint8_t[504U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_504size_t(
    uint8_t randomness[4U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)504U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static KRML_MUSTINLINE void shake128_squeeze_block___4size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_block___4size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[4U][168U]) {
  uint8_t ret0[4U][168U];
  shake128_squeeze_block___4size_t(self, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(uint8_t[168U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_168size_t(
    uint8_t randomness[4U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)168U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t0(
    int16_t s[272U]) {
  return from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      Eurydice_array_to_subslice((size_t)272U, s,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)256U}),
                                 int16_t, core_ops_range_Range__size_t,
                                 Eurydice_slice));
}

static KRML_MUSTINLINE void
sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
    uint8_t seeds[4U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, seeds, (size_t)4U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb___4size_t0(uu____0);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_three_blocks___4size_t0(&xof_state, randomness0);
  uint8_t uu____1[4U][504U];
  memcpy(uu____1, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done =
      sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_504size_t(
          uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      shake128_squeeze_block___4size_t0(&xof_state, randomness);
      uint8_t uu____2[4U][168U];
      memcpy(uu____2, randomness, (size_t)4U * sizeof(uint8_t[168U]));
      done =
          sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_168size_t(
              uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[4U][272U];
  memcpy(uu____3, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      ret0[i] =
          closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t0(
              uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void
sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U][4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[4U][4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
          A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          sampled[4U];
      sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
          uu____1, sampled);
      for (
          size_t i = (size_t)0U;
          i <
          core_slice___Slice_T___len(
              Eurydice_array_to_slice(
                  (size_t)4U, sampled,
                  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                  Eurydice_slice),
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              size_t);
          i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(
      ret, A_transpose,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
}

typedef struct
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      fst[4U];
  uint8_t snd;
} __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t;

static KRML_MUSTINLINE void PRFxN___4size_t_128size_t(uint8_t (*input)[33U],
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

static KRML_MUSTINLINE void PRFxN___4size_t_128size_t0(uint8_t (*input)[33U],
                                                       uint8_t ret[4U][128U]) {
  uint8_t ret0[4U][128U];
  PRFxN___4size_t_128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(uint8_t[128U]));
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
    sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re_as_ntt[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      re_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___4size_t_128size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
                  Eurydice_array_to_slice((size_t)128U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          &re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[4U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE void
add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)16U, self->coefficients, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t);
       i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            self->coefficients[i0], &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

static KRML_MUSTINLINE void
compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)4U, matrix_A,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [4U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = matrix_A[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)4U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *matrix_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              matrix_element, &s_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          &result[i1], &product);
    }
    add_standard_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t__
generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G___4size_t(key_generation_seed, hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          (size_t)32U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[4U][4U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed_for_A0, ret);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
      ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(seed_for_secret_and_error,
                                                    prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
      uu____2 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
              uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[4U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_as_ntt[4U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
          uu____3, domain_separator)
          .fst,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[4U];
  compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
      A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____4[4U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[4U][4U];
  memcpy(
      uu____5, A_transpose,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(
      pk.A, uu____5,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____7[4U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  return (CLITERAL(
      __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t__){
      .fst = sk, .snd = pk});
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_3168size_t_1568size_t_1536size_t_2size_t_128size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void H___4size_t(Eurydice_slice input,
                                        uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_avx2_H(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_3168size_t_1568size_t_1536size_t_2size_t_128size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
              ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[4U][4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_3168size_t_1568size_t_1536size_t_2size_t_128size_t(
          A[i]););
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              uu____1 = clone__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                  &ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[4U][4U];
  memcpy(
      uu____2, A,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  memcpy(
      ind_cpa_public_key.A, uu____2,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  uint8_t pk_serialized[1568U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t_1568size_t(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H___4size_t(Eurydice_array_to_slice((size_t)1568U, pk_serialized, uint8_t,
                                      Eurydice_slice),
              public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      uu____3 = ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      uu____6 = ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

static libcrux_ml_kem_utils_extraction_helper_Keypair1024
generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_1568size_t_1536size_t_2size_t_128size_t(
    Eurydice_slice key_generation_seed) {
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___4size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
              key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      pk = uu____0.snd;
  uint8_t public_key_serialized[1568U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t_1568size_t(
      pk.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t,
                              Eurydice_slice),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1536size_t(
      sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[1536U];
  memcpy(uu____1, secret_key_serialized, (size_t)1536U * sizeof(uint8_t));
  uint8_t uu____2[1568U];
  memcpy(uu____2, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 lit;
  memcpy(lit.fst, uu____1, (size_t)1536U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_3168size_t(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[3168U]) {
  uint8_t out[3168U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)3168U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____1,
              .end = uu____2 +
                     core_slice___Slice_T___len(private_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)3168U, uu____3,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____4,
              .end = uu____5 +
                     core_slice___Slice_T___len(public_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice(
      (size_t)3168U, out,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = pointer,
          .end = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[32U];
  H___4size_t(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)3168U, uu____7,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____8,
              .end = uu____9 + core_slice___Slice_T___len(
                                   implicit_rejection_value, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
  memcpy(ret, out, (size_t)3168U * sizeof(uint8_t));
}

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_3168size_t_1568size_t_1536size_t_2size_t_128size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1536size_t_1568size_t_1536size_t_2size_t_128size_t(
          ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_3168size_t(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[3168U];
  memcpy(uu____1, secret_key_serialized, (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____3168size_t private_key =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___3168size_t(
          uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey____3168size_t uu____2 = private_key;
  uint8_t uu____3[1568U];
  memcpy(uu____3, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___3168size_t_1568size_t(
      uu____2,
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1568size_t(
          uu____3));
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
    sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_128size_t_2size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      error_1[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___4size_t_128size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
                  Eurydice_array_to_slice((size_t)128U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[4U];
  memcpy(
      uu____2, error_1,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE void PRF___4size_t_128size_t(Eurydice_slice input,
                                                    uint8_t ret[128U]) {
  uint8_t ret0[128U];
  PRF___128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)128U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)7U);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE void
compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)4U, a_as_ntt,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [4U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = a_as_ntt[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)4U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              a_element, &r_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          &result[i1], &product);
    }
    invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
        &result[i1]);
    add_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(&result[i1],
                                                               &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *t_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *r_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *error_2,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &t_as_ntt[i0], &r_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
      &result);
  result = add_message_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      error_2, message, result);
  return result;
}

static KRML_MUSTINLINE void
compress_then_serialize_11__libcrux_ml_kem_vector_avx2_SIMD256Vector_352size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
    uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    uint8_t coefficient = compress___11int32_t(
        to_unsigned_representative__libcrux_ml_kem_vector_avx2_SIMD256Vector(
            re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_11(
        coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)352U, serialized,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = (size_t)22U * i0, .end = (size_t)22U * i0 + (size_t)22U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)22U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, serialized, (size_t)352U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
compress_then_serialize_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t_352size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re,
    uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11__libcrux_ml_kem_vector_avx2_SIMD256Vector_352size_t(
      re, uu____0);
  memcpy(ret, uu____0, (size_t)352U * sizeof(uint8_t));
}

static void
compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1408size_t_11size_t_352size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        input[4U],
    Eurydice_slice out) {
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)4U, input,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * ((size_t)1408U / (size_t)4U),
            .end = (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U)}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[352U];
    compress_then_serialize_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t_352size_t(
        &re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)352U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
compress_then_serialize_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_5size_t_160size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re,
    Eurydice_slice out) {
  compress_then_serialize_5__libcrux_ml_kem_vector_avx2_SIMD256Vector(re, out);
}

static void
encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
        *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
      uu____1 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_2size_t_128size_t(
              uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t__uint8_t
      uu____3 =
          sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_128size_t_2size_t(
              uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[4U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF___4size_t_128size_t(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_2 =
          sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
              Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t,
                                      Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u[4U];
  compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
      public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message_as_ring_element =
          deserialize_then_decompress_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          public_key->t_as_ntt, r_as_ntt, &error_2, &message_as_ring_element);
  uint8_t ciphertext[1568U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[4U];
  memcpy(
      uu____5, u,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1408size_t_11size_t_352size_t(
      uu____5, Eurydice_array_to_subslice(
                   (size_t)1568U, ciphertext,
                   (CLITERAL(core_ops_range_Range__size_t){
                       .start = (size_t)0U, .end = (size_t)1408U}),
                   uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____6 = v;
  compress_then_serialize_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_5size_t_160size_t(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
        *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___4size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      *uu____2 = &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1568size_t(
          uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1536size_t_4size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
    Eurydice_slice public_key, uint8_t message[32U], Eurydice_slice randomness,
    uint8_t ret[1568U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[4U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_1536size_t_4size_t(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[4U][4U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed, ret0);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
      ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[4U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____1[4U][4U];
  memcpy(
      uu____1, A,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(
      public_key_unpacked.A, uu____1,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [4U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      *uu____3 = &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1568U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
      uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1568U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t(
    Eurydice_slice shared_secret, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_4size_t_1568size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H___4size_t(
      Eurydice_array_to_slice(
          (size_t)1568U,
          libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1568size_t(
              public_key),
          uint8_t, Eurydice_slice),
      ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G___4size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1568U,
      libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1568size_t(
          public_key),
      uint8_t, Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext ciphertext0 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1568size_t(
          uu____4);
  uint8_t shared_secret_array[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t(
      shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      deserialize_then_decompress_11__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          serialized);
  return uu____0;
}

static KRML_MUSTINLINE void
ntt_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)7U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)6U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)5U);
  ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re,
                                                                (size_t)4U);
  ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE void
deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_11size_t(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      u_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice(
        (size_t)1568U, ciphertext,
        (CLITERAL(core_ops_range_Range__size_t){
            .start =
                i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                      (size_t)11U / (size_t)8U),
            .end = i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                         (size_t)11U / (size_t)8U) +
                   LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                       (size_t)11U / (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_then_decompress_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t(
                u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_11size_t(
        &u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    deserialize_then_decompress_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_5size_t(
        Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      deserialize_then_decompress_5__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          serialized);
  return uu____0;
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *v,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *secret_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &secret_as_ntt[i0], &u_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
      &result);
  result = subtract_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(v, result);
  return result;
}

static void
decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_1408size_t_11size_t_5size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
        *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[4U];
  deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_11size_t(
      ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = deserialize_then_decompress_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_5size_t(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message =
          compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
              &v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void PRF___4size_t_32size_t(Eurydice_slice input,
                                                   uint8_t ret[32U]) {
  uint8_t ret0[32U];
  PRF___32size_t(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_3168size_t_1536size_t_1568size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t_1600size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_1408size_t_11size_t_5size_t(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___4size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array___1600size_t(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF___4size_t_32size_t(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      *uu____3 = &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
      uu____3, uu____4, pseudorandomness, expected_ciphertext);
  Eurydice_slice uu____5 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
          ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          uu____5, Eurydice_array_to_slice((size_t)1568U, expected_ciphertext,
                                           uint8_t, Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[4U];
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U,
      secret_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice(
        secret_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_1408size_t_11size_t_5size_t(
    Eurydice_slice secret_key, uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[4U];
  deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
      secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[4U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)4U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t ret0[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_1408size_t_11size_t_5size_t(
      &secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_4size_t_3168size_t_1536size_t_1568size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t_1600size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t,
                                  Eurydice_slice),
          (size_t)1536U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          secret_key0, (size_t)1568U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____2 =
      core_slice___Slice_T___split_at(
          secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_1568size_t_1408size_t_11size_t_5size_t(
      ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G___4size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____3 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array___1600size_t(implicit_rejection_value,
                                                      to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF___4size_t_32size_t(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t_1536size_t_1408size_t_160size_t_11size_t_5size_t_352size_t_2size_t_128size_t_2size_t_128size_t(
      uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_4size_t_1568size_t(
      shared_secret0, shared_secret);
  Eurydice_slice uu____7 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
          ciphertext);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____7,
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_800size_t_2size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void
serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *key,
    uint8_t ret[768U]) {
  uint8_t out[768U] = {0U};
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)2U, key,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice(
        (size_t)768U, out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = (i0 + (size_t)1U) *
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)768U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice(
      (size_t)800U, public_key_serialized,
      (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                              .end = (size_t)768U}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[768U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t(
      t_as_ntt, ret0);
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

bool libcrux_ml_kem_ind_cca_validate_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[2U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_800size_t_2size_t(
      Eurydice_array_to_subslice_to((size_t)800U, public_key, (size_t)768U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
      uu____0,
      Eurydice_array_to_subslice_from((size_t)800U, public_key, (size_t)768U,
                                      uint8_t, size_t, Eurydice_slice),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)800U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

typedef struct
    __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      snd;
} __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t__;

static KRML_MUSTINLINE void G___2size_t(Eurydice_slice input,
                                        uint8_t ret[64U]) {
  uint8_t ret0[64U];
  libcrux_ml_kem_hash_functions_avx2_G(input, ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___2size_t(uint8_t input[2U][34U]) {
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice));
  return state;
}

static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
shake128_init_absorb___2size_t0(uint8_t input[2U][34U]) {
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb___2size_t(uu____0);
}

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___2size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_three_blocks___2size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][504U]) {
  uint8_t ret0[2U][504U];
  shake128_squeeze_three_blocks___2size_t(self, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(uint8_t[504U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_504size_t(
    uint8_t randomness[2U][504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)504U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static KRML_MUSTINLINE void shake128_squeeze_block___2size_t(
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

static KRML_MUSTINLINE void shake128_squeeze_block___2size_t0(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t ret[2U][168U]) {
  uint8_t ret0[2U][168U];
  shake128_squeeze_block___2size_t(self, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(uint8_t[168U]));
}

static KRML_MUSTINLINE bool
sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_168size_t(
    uint8_t randomness[2U][168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          Eurydice_slice uu____0 = Eurydice_array_to_subslice(
              (size_t)168U, randomness[i1],
              (CLITERAL(core_ops_range_Range__size_t){
                  .start = r * (size_t)24U,
                  .end = r * (size_t)24U + (size_t)24U}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
          size_t sampled =
              libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
                  uu____0,
                  Eurydice_array_to_subslice(
                      (size_t)272U, out[i1],
                      (CLITERAL(core_ops_range_Range__size_t){
                          .start = sampled_coefficients[i1],
                          .end = sampled_coefficients[i1] + (size_t)16U}),
                      int16_t, core_ops_range_Range__size_t, Eurydice_slice));
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

static libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t0(
    int16_t s[272U]) {
  return from_i16_array__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      Eurydice_array_to_subslice((size_t)272U, s,
                                 (CLITERAL(core_ops_range_Range__size_t){
                                     .start = (size_t)0U, .end = (size_t)256U}),
                                 int16_t, core_ops_range_Range__size_t,
                                 Eurydice_slice));
}

static KRML_MUSTINLINE void
sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
    uint8_t seeds[2U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, seeds, (size_t)2U * sizeof(uint8_t[34U]));
  libcrux_sha3_avx2_x4_incremental_KeccakState xof_state =
      shake128_init_absorb___2size_t0(uu____0);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_three_blocks___2size_t0(&xof_state, randomness0);
  uint8_t uu____1[2U][504U];
  memcpy(uu____1, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done =
      sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_504size_t(
          uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      shake128_squeeze_block___2size_t0(&xof_state, randomness);
      uint8_t uu____2[2U][168U];
      memcpy(uu____2, randomness, (size_t)2U * sizeof(uint8_t[168U]));
      done =
          sample_from_uniform_distribution_next__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_168size_t(
              uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[2U][272U];
  memcpy(uu____3, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      ret0[i] =
          closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t0(
              uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void
sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U][2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[2U][2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
          A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          sampled[2U];
      sample_from_xof__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
          uu____1, sampled);
      for (
          size_t i = (size_t)0U;
          i <
          core_slice___Slice_T___len(
              Eurydice_array_to_slice(
                  (size_t)2U, sampled,
                  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                  Eurydice_slice),
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              size_t);
          i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(
      ret, A_transpose,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
}

typedef struct
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      fst[2U];
  uint8_t snd;
} __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t;

static KRML_MUSTINLINE void PRFxN___2size_t_192size_t(uint8_t (*input)[33U],
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

static KRML_MUSTINLINE void PRFxN___2size_t_192size_t0(uint8_t (*input)[33U],
                                                       uint8_t ret[2U][192U]) {
  uint8_t ret0[2U][192U];
  PRFxN___2size_t_192size_t(input, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(uint8_t[192U]));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
        Eurydice_slice randomness) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0;
  uu____0 =
      sample_from_binomial_distribution_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          randomness);
  return uu____0;
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
    sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      re_as_ntt[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      re_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___2size_t_192size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_3size_t(
                  Eurydice_array_to_slice((size_t)192U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
          &re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[2U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE void
add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)16U, self->coefficients, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t);
       i++) {
    size_t i0 = i;
    uint8_t uu____0 =
        libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
            self->coefficients[i0], &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

static KRML_MUSTINLINE void
compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)2U, matrix_A,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [2U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = matrix_A[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)2U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *matrix_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              matrix_element, &s_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
          &result[i1], &product);
    }
    add_standard_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
        &result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t__
generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G___2size_t(key_generation_seed, hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          (size_t)32U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A_transpose[2U][2U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed_for_A0, ret);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
      ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(seed_for_secret_and_error,
                                                    prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
      uu____2 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
              uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[2U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_as_ntt[2U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
          uu____3, domain_separator)
          .fst,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[2U];
  compute_As_plus_e__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
      A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____4[2U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[2U][2U];
  memcpy(
      uu____5, A_transpose,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(
      pk.A, uu____5,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____7[2U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  return (CLITERAL(
      __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t__){
      .fst = sk, .snd = pk});
}

static void
closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  memcpy(
      ret, ret0,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE void H___2size_t(Eurydice_slice input,
                                        uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_avx2_H(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
              ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[2U][2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      closure__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
          A[i]););
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              uu____1 = clone__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                  &ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[2U][2U];
  memcpy(
      uu____2, A,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  memcpy(
      ind_cpa_public_key.A, uu____2,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  uint8_t pk_serialized[800U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H___2size_t(Eurydice_array_to_slice((size_t)800U, pk_serialized, uint8_t,
                                      Eurydice_slice),
              public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      uu____3 = ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      uu____6 = ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

static libcrux_ml_kem_utils_extraction_helper_Keypair512
generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_800size_t_768size_t_3size_t_192size_t(
    Eurydice_slice key_generation_seed) {
  __libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t___libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_libcrux_ml_kem_vector_avx2_SIMD256Vector___2size_t__
      uu____0 =
          generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
              key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      pk = uu____0.snd;
  uint8_t public_key_serialized[800U];
  serialize_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
      pk.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, pk.seed_for_A, uint8_t,
                              Eurydice_slice),
      public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t(
      sk.secret_as_ntt, secret_key_serialized);
  uint8_t uu____1[768U];
  memcpy(uu____1, secret_key_serialized, (size_t)768U * sizeof(uint8_t));
  uint8_t uu____2[800U];
  memcpy(uu____2, public_key_serialized, (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair512 lit;
  memcpy(lit.fst, uu____1, (size_t)768U * sizeof(uint8_t));
  memcpy(lit.snd, uu____2, (size_t)800U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_1632size_t(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[1632U]) {
  uint8_t out[1632U] = {0U};
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = out;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)1632U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____1,
              .end = uu____2 +
                     core_slice___Slice_T___len(private_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      private_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(private_key, uint8_t, size_t);
  uint8_t *uu____3 = out;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)1632U, uu____3,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____4,
              .end = uu____5 +
                     core_slice___Slice_T___len(public_key, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      public_key, uint8_t, void *);
  pointer = pointer + core_slice___Slice_T___len(public_key, uint8_t, size_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice(
      (size_t)1632U, out,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = pointer,
          .end = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  uint8_t ret0[32U];
  H___2size_t(public_key, ret0);
  core_slice___Slice_T___copy_from_slice(
      uu____6,
      Eurydice_array_to_slice((size_t)32U, ret0, uint8_t, Eurydice_slice),
      uint8_t, void *);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = out;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)1632U, uu____7,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = uu____8,
              .end = uu____9 + core_slice___Slice_T___len(
                                   implicit_rejection_value, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      implicit_rejection_value, uint8_t, void *);
  memcpy(ret, out, (size_t)1632U * sizeof(uint8_t));
}

libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_ind_cca_generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
    uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice(
      (size_t)64U, randomness,
      (CLITERAL(core_ops_range_Range__size_t){
          .start = (size_t)0U,
          .end = LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}),
      uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_800size_t_768size_t_3size_t_192size_t(
          ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_1632size_t(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[1632U];
  memcpy(uu____1, secret_key_serialized, (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____1632size_t private_key =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___1632size_t(
          uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey____1632size_t uu____2 = private_key;
  uint8_t uu____3[800U];
  memcpy(uu____3, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___1632size_t_800size_t(
      uu____2,
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___800size_t(
          uu____3));
}

static KRML_MUSTINLINE void PRFxN___2size_t_128size_t(uint8_t (*input)[33U],
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

static KRML_MUSTINLINE void PRFxN___2size_t_128size_t0(uint8_t (*input)[33U],
                                                       uint8_t ret[2U][128U]) {
  uint8_t ret0[2U][128U];
  PRFxN___2size_t_128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(uint8_t[128U]));
}

static KRML_MUSTINLINE
    __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
    sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_128size_t_2size_t(
        uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      error_1[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
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
  PRFxN___2size_t_128size_t0(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          uu____1 =
              sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
                  Eurydice_array_to_slice((size_t)128U, prf_outputs[i0],
                                          uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____2[2U];
  memcpy(
      uu____2, error_1,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
      lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  lit.snd = domain_separator;
  return lit;
}

static KRML_MUSTINLINE void PRF___2size_t_128size_t(Eurydice_slice input,
                                                    uint8_t ret[128U]) {
  uint8_t ret0[128U];
  PRF___128size_t(input, ret0);
  memcpy(ret, ret0, (size_t)128U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_2__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_3__libcrux_ml_kem_vector_avx2_SIMD256Vector(&zeta_i, re);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      &zeta_i, re, (size_t)7U);
  poly_barrett_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(re);
}

static KRML_MUSTINLINE void
compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector (
        *a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      result[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (
      size_t i0 = (size_t)0U;
      i0 <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)2U, a_as_ntt,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U],
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
              [2U],
          size_t);
      i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        *row = a_as_ntt[i1];
    for (
        size_t i = (size_t)0U;
        i <
        core_slice___Slice_T___len(
            Eurydice_array_to_slice(
                (size_t)2U, row,
                libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
                Eurydice_slice),
            libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
            size_t);
        i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              a_element, &r_as_ntt[j]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
          &result[i1], &product);
    }
    invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
        &result[i1]);
    add_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(&result[i1],
                                                               &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *t_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *r_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *error_2,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &t_as_ntt[i0], &r_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
      &result);
  result = add_message_error_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      error_2, message, result);
  return result;
}

static void
compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_640size_t_10size_t_320size_t(
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        input[2U],
    Eurydice_slice out) {
  for (
      size_t i = (size_t)0U;
      i <
      core_slice___Slice_T___len(
          Eurydice_array_to_slice(
              (size_t)2U, input,
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
              Eurydice_slice),
          libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector,
          size_t);
      i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * ((size_t)640U / (size_t)2U),
            .end = (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U)}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t_320size_t(
        &re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static void
encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array___33size_t(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
      uu____1 =
          sample_vector_cbd_then_ntt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_3size_t_192size_t(
              uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  __libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t__uint8_t
      uu____3 =
          sample_ring_element_cbd__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_128size_t_2size_t(
              uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_1[2U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF___2size_t_128size_t(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      error_2 =
          sample_from_binomial_distribution__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
              Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t,
                                      Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u[2U];
  compute_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
      public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message_as_ring_element =
          deserialize_then_decompress_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = compute_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
          public_key->t_as_ntt, r_as_ntt, &error_2, &message_as_ring_element);
  uint8_t ciphertext[768U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____5[2U];
  memcpy(
      uu____5, u,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  compress_then_serialize_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_640size_t_10size_t_320size_t(
      uu____5, Eurydice_array_to_subslice(
                   (size_t)768U, ciphertext,
                   (CLITERAL(core_ops_range_Range__size_t){
                       .start = (size_t)0U, .end = (size_t)640U}),
                   uint8_t, core_ops_range_Range__size_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____6 = v;
  compress_then_serialize_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t_128size_t(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___2size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      *uu____2 = &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext____768size_t uu____5 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___768size_t(
          uu____4);
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_768size_t_2size_t(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      deserialized_pk[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      deserialized_pk[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(public_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice(
        public_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_reduced_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    Eurydice_slice public_key, uint8_t message[32U], Eurydice_slice randomness,
    uint8_t ret[768U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[2U];
  deserialize_ring_elements_reduced__libcrux_ml_kem_vector_avx2_SIMD256Vector_768size_t_2size_t(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[2U][2U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array___34size_t(seed, ret0);
  sample_matrix_A__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
      ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
      dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[2U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____1[2U][2U];
  memcpy(
      uu____1, A,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(
      public_key_unpacked.A, uu____1,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
                  [2U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      *uu____3 = &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[768U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)768U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t(
    Eurydice_slice shared_secret, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H___2size_t(
      Eurydice_array_to_slice(
          (size_t)800U,
          libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___800size_t(
              public_key),
          uint8_t, Eurydice_slice),
      ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G___2size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)800U,
      libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___800size_t(
          public_key),
      uint8_t, Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext____768size_t ciphertext0 =
      libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___768size_t(
          uu____4);
  uint8_t shared_secret_array[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t(
      shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext____768size_t uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_ lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_10size_t(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      u_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice((size_t)768U, ciphertext, uint8_t,
                                       Eurydice_slice),
               uint8_t, size_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice(
        (size_t)768U, ciphertext,
        (CLITERAL(core_ops_range_Range__size_t){
            .start =
                i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                      (size_t)10U / (size_t)8U),
            .end = i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                         (size_t)10U / (size_t)8U) +
                   LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                       (size_t)10U / (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_then_decompress_ring_element_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
                u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_10size_t(
        &u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static KRML_MUSTINLINE
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
    compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *v,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *secret_as_ntt,
        libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
            *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      result = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector();
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
          product = ntt_multiply__libcrux_ml_kem_vector_avx2_SIMD256Vector(
              &secret_as_ntt[i0], &u_as_ntt[i0]);
      add_to_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
          &result, &product););
  invert_ntt_montgomery__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
      &result);
  result = subtract_reduce__libcrux_ml_kem_vector_avx2_SIMD256Vector(v, result);
  return result;
}

static void
decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_640size_t_10size_t_4size_t(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      u_as_ntt[2U];
  deserialize_then_decompress_u__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_10size_t(
      ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      v = deserialize_then_decompress_ring_element_v__libcrux_ml_kem_vector_avx2_SIMD256Vector_4size_t(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      message =
          compute_message__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
              &v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message__libcrux_ml_kem_vector_avx2_SIMD256Vector(
      message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void PRF___2size_t_32size_t(Eurydice_slice input,
                                                   uint8_t ret[32U]) {
  uint8_t ret0[32U];
  PRF___32size_t(input, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_640size_t_10size_t_4size_t(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
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
  G___2size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array___800size_t(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF___2size_t_32size_t(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      *uu____3 = &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____3, uu____4, pseudorandomness, expected_ciphertext);
  Eurydice_slice uu____5 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
          ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          uu____5, Eurydice_array_to_slice((size_t)768U, expected_ciphertext,
                                           uint8_t, Eurydice_slice));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void
deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[2U];
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U,
      secret_as_ntt[i] = ZERO__libcrux_ml_kem_vector_avx2_SIMD256Vector(););
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(secret_key, uint8_t, size_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice secret_bytes = Eurydice_slice_subslice(
        secret_key,
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
        uu____0 =
            deserialize_to_uncompressed_ring_element__libcrux_ml_kem_vector_avx2_SIMD256Vector(
                secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
}

static void
decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_640size_t_10size_t_4size_t(
    Eurydice_slice secret_key, uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[2U];
  deserialize_secret_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t(
      secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      uu____0[2U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)2U *
          sizeof(
              libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector));
  uint8_t ret0[32U];
  decrypt_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_640size_t_10size_t_4size_t(
      &secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_ind_cca_decapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t,
                                  Eurydice_slice),
          (size_t)768U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____1 =
      core_slice___Slice_T___split_at(
          secret_key0, (size_t)800U, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____2 =
      core_slice___Slice_T___split_at(
          secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  uint8_t decrypted[32U];
  decrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_640size_t_10size_t_4size_t(
      ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array___64size_t(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G___2size_t(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____3 =
      core_slice___Slice_T___split_at(
          Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
          LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array___800size_t(implicit_rejection_value,
                                                     to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4,
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
          ciphertext),
      uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF___2size_t_32size_t(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf__libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t(
      shared_secret0, shared_secret);
  Eurydice_slice uu____7 =
      libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
          ciphertext);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____7,
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}
