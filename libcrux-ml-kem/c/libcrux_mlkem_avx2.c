/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 564ce891b07fd4aefe7d5ccd78e61400b4ac4a2b
 * Karamel: 06a6d2fb3a547d11c9f6dbec26f1f9b5e0dbf411
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#include "internal/libcrux_mlkem_avx2.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"
#include "libcrux_sha3_avx2.h"
#include "libcrux_sha3_portable.h"

KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input) {
  libcrux_sha3_Sha3_512Digest digest = {.data = {0U}};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, &digest, uint8_t), input);
  return digest;
}

KRML_MUSTINLINE Eurydice_arr_60
libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, &digest, uint8_t), input);
  return digest;
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_vec_zero(void) {
  return mm256_setzero_si256();
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ZERO_f5(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array) {
  return mm256_loadu_si256_i16(array);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_i16_array_f5(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_vec_from_i16_array(array);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_avx2_vec_to_i16_array(__m256i v) {
  Eurydice_arr_e2 output = {.data = {0U}};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, &output, int16_t),
                         v);
  return output;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_avx2_to_i16_array_f5(__m256i x) {
  return libcrux_ml_kem_vector_avx2_vec_to_i16_array(x);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_bytes(Eurydice_slice array) {
  return mm256_loadu_si256_u8(
      Eurydice_slice_subslice3(array, (size_t)0U, (size_t)32U, uint8_t *));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_from_bytes_f5(Eurydice_slice array) {
  return libcrux_ml_kem_vector_avx2_from_bytes(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_bytes(__m256i x,
                                                         Eurydice_slice bytes) {
  mm256_storeu_si256_u8(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)32U, uint8_t *), x);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_to_bytes_f5(
    __m256i x, Eurydice_slice bytes) {
  libcrux_ml_kem_vector_avx2_to_bytes(x, bytes);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_add_epi16(lhs, rhs);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_add_f5(__m256i lhs,
                                                          __m256i *rhs) {
  return libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs[0U]);
}

KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs,
                                                                  __m256i rhs) {
  return mm256_sub_epi16(lhs, rhs);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_sub_f5(__m256i lhs,
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_multiply_by_constant_f5(__m256i vec, int16_t c) {
  return libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(vec, c);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_cond_subtract_3329_f5(__m256i vector) {
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_barrett_reduce_f5(__m256i vector) {
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
    __m256i vector, int16_t constant) {
  return libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
      vector, constant);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant) {
  __m256i cv = mm256_set1_epi16(constant);
  return mm256_and_si256(vector, cv);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE __m256i shift_right_ef(__m256i vector) {
  return mm256_srai_epi16((int32_t)15, vector, __m256i);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_to_unsigned_representative(__m256i a) {
  __m256i t = shift_right_ef(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_avx2_arithmetic_add(a, fm);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(__m256i a) {
  return libcrux_ml_kem_vector_avx2_arithmetic_to_unsigned_representative(a);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_1_f5(__m256i vector) {
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
libcrux_ml_kem_vector_avx2_compress_decompress_1(__m256i a) {
  __m256i z = mm256_setzero_si256();
  __m256i s = libcrux_ml_kem_vector_avx2_arithmetic_sub(z, a);
  return libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      s, (int16_t)1665);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_decompress_1_f5(__m256i a) {
  return libcrux_ml_kem_vector_avx2_compress_decompress_1(a);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_f5(
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_f5(
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_ntt_layer_3_step_f5(__m256i vector, int16_t zeta) {
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_f5(
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_f5(
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_f5(
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ntt_multiply_f5(
    __m256i *lhs, __m256i *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_avx2_ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2,
                                                 zeta3);
}

KRML_MUSTINLINE Eurydice_arr_8b
libcrux_ml_kem_vector_avx2_serialize_serialize_1(__m256i vector) {
  __m256i lsb_to_msb = mm256_slli_epi16((int32_t)15, vector, __m256i);
  __m128i low_msbs = mm256_castsi256_si128(lsb_to_msb);
  __m128i high_msbs = mm256_extracti128_si256((int32_t)1, lsb_to_msb, __m128i);
  __m128i msbs = mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = mm_movemask_epi8(msbs);
  Eurydice_arr_8b result = {
      .data = {(uint8_t)bits_packed, (uint8_t)(bits_packed >> 8U)}};
  return result;
}

KRML_MUSTINLINE Eurydice_arr_8b
libcrux_ml_kem_vector_avx2_serialize_1(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_8b
libcrux_ml_kem_vector_avx2_serialize_1_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_1(vector);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_1_f5(Eurydice_slice bytes) {
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

KRML_MUSTINLINE Eurydice_arr_c4
libcrux_ml_kem_vector_avx2_serialize_serialize_4(__m256i vector) {
  Eurydice_arr_88 serialized = {.data = {0U}};
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
      Eurydice_array_to_slice((size_t)16U, &serialized, uint8_t), combined0);
  core_result_Result_a4 dst;
  Eurydice_slice_to_array2(&dst,
                           Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                       (size_t)8U, uint8_t *),
                           Eurydice_slice, Eurydice_arr_c4,
                           core_array_TryFromSliceError);
  return core_result_unwrap_26_ab(dst);
}

KRML_MUSTINLINE Eurydice_arr_c4
libcrux_ml_kem_vector_avx2_serialize_4(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_c4
libcrux_ml_kem_vector_avx2_serialize_4_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_4(vector);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_4_f5(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_4(bytes);
}

KRML_MUSTINLINE Eurydice_arr_77
libcrux_ml_kem_vector_avx2_serialize_serialize_5(__m256i vector) {
  Eurydice_arr_60 serialized = {.data = {0U}};
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
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                    (size_t)16U, uint8_t *),
                        lower_8);
  __m128i upper_8 =
      mm256_extracti128_si256((int32_t)1, adjacent_8_combined1, __m128i);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)5U,
                                                    (size_t)21U, uint8_t *),
                        upper_8);
  core_result_Result_1c dst;
  Eurydice_slice_to_array2(&dst,
                           Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                       (size_t)10U, uint8_t *),
                           Eurydice_slice, Eurydice_arr_77,
                           core_array_TryFromSliceError);
  return core_result_unwrap_26_3d(dst);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_77
libcrux_ml_kem_vector_avx2_serialize_5_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_5(vector);
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
  __m128i coefficients = mm_set_epi8(
      (int8_t)Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int8_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_5_f5(Eurydice_slice bytes) {
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
  return (KRML_CLITERAL(core_core_arch_x86___m128i_x2){.fst = lower_8,
                                                       .snd = upper_8});
}

KRML_MUSTINLINE Eurydice_arr_dc
libcrux_ml_kem_vector_avx2_serialize_serialize_10(__m256i vector) {
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
          vector);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  Eurydice_arr_60 serialized = {.data = {0U}};
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                    (size_t)16U, uint8_t *),
                        lower_8);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)10U,
                                                    (size_t)26U, uint8_t *),
                        upper_8);
  core_result_Result_6e dst;
  Eurydice_slice_to_array2(&dst,
                           Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                       (size_t)20U, uint8_t *),
                           Eurydice_slice, Eurydice_arr_dc,
                           core_array_TryFromSliceError);
  return core_result_unwrap_26_51(dst);
}

KRML_MUSTINLINE Eurydice_arr_dc
libcrux_ml_kem_vector_avx2_serialize_10(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_dc
libcrux_ml_kem_vector_avx2_serialize_10_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_10(vector);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients =
      mm_shuffle_epi8(lower_coefficients0,
                      mm_set_epi8((int8_t)9, (int8_t)8, (int8_t)8, (int8_t)7,
                                  (int8_t)7, (int8_t)6, (int8_t)6, (int8_t)5,
                                  (int8_t)4, (int8_t)3, (int8_t)3, (int8_t)2,
                                  (int8_t)2, (int8_t)1, (int8_t)1, (int8_t)0));
  __m128i upper_coefficients = mm_shuffle_epi8(
      upper_coefficients0,
      mm_set_epi8((int8_t)15, (int8_t)14, (int8_t)14, (int8_t)13, (int8_t)13,
                  (int8_t)12, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9,
                  (int8_t)9, (int8_t)8, (int8_t)8, (int8_t)7, (int8_t)7,
                  (int8_t)6));
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
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)16U, uint8_t *);
  Eurydice_slice upper_coefficients =
      Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)20U, uint8_t *);
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
      mm_loadu_si128(lower_coefficients), mm_loadu_si128(upper_coefficients));
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_10(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_10_f5(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_deserialize_10(bytes);
}

KRML_MUSTINLINE Eurydice_arr_f3
libcrux_ml_kem_vector_avx2_serialize_serialize_11(__m256i vector) {
  Eurydice_arr_e2 array = {.data = {0U}};
  mm256_storeu_si256_i16(Eurydice_array_to_slice((size_t)16U, &array, int16_t),
                         vector);
  Eurydice_arr_e2 input = libcrux_ml_kem_vector_portable_from_i16_array_b8(
      Eurydice_array_to_slice((size_t)16U, &array, int16_t));
  return libcrux_ml_kem_vector_portable_serialize_11_b8(input);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_f3
libcrux_ml_kem_vector_avx2_serialize_11_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_11(vector);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes) {
  Eurydice_arr_e2 output =
      libcrux_ml_kem_vector_portable_deserialize_11_b8(bytes);
  Eurydice_arr_e2 array =
      libcrux_ml_kem_vector_portable_to_i16_array_b8(output);
  return mm256_loadu_si256_i16(
      Eurydice_array_to_slice((size_t)16U, &array, int16_t));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_11_f5(Eurydice_slice bytes) {
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
  return (KRML_CLITERAL(core_core_arch_x86___m128i_x2){.fst = lower_8,
                                                       .snd = upper_8});
}

KRML_MUSTINLINE Eurydice_arr_6d
libcrux_ml_kem_vector_avx2_serialize_serialize_12(__m256i vector) {
  Eurydice_arr_60 serialized = {.data = {0U}};
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
          vector);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                    (size_t)16U, uint8_t *),
                        lower_8);
  mm_storeu_bytes_si128(Eurydice_array_to_subslice3(&serialized, (size_t)12U,
                                                    (size_t)28U, uint8_t *),
                        upper_8);
  core_result_Result_16 dst;
  Eurydice_slice_to_array2(&dst,
                           Eurydice_array_to_subslice3(&serialized, (size_t)0U,
                                                       (size_t)24U, uint8_t *),
                           Eurydice_slice, Eurydice_arr_6d,
                           core_array_TryFromSliceError);
  return core_result_unwrap_26_a9(dst);
}

KRML_MUSTINLINE Eurydice_arr_6d
libcrux_ml_kem_vector_avx2_serialize_12(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE Eurydice_arr_6d
libcrux_ml_kem_vector_avx2_serialize_12_f5(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_serialize_12(vector);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients =
      mm_shuffle_epi8(lower_coefficients0,
                      mm_set_epi8((int8_t)11, (int8_t)10, (int8_t)10, (int8_t)9,
                                  (int8_t)8, (int8_t)7, (int8_t)7, (int8_t)6,
                                  (int8_t)5, (int8_t)4, (int8_t)4, (int8_t)3,
                                  (int8_t)2, (int8_t)1, (int8_t)1, (int8_t)0));
  __m128i upper_coefficients = mm_shuffle_epi8(
      upper_coefficients0,
      mm_set_epi8((int8_t)15, (int8_t)14, (int8_t)14, (int8_t)13, (int8_t)12,
                  (int8_t)11, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
                  (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)5, (int8_t)5,
                  (int8_t)4));
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
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)16U, uint8_t *));
  __m128i upper_coefficients = mm_loadu_si128(
      Eurydice_slice_subslice3(bytes, (size_t)8U, (size_t)24U, uint8_t *));
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
      lower_coefficients, upper_coefficients);
}

KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_12(Eurydice_slice bytes) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_deserialize_12_f5(Eurydice_slice bytes) {
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
  Eurydice_arr_8b good = libcrux_ml_kem_vector_avx2_serialize_serialize_1(
      compare_with_field_modulus);
  Eurydice_arr_88 lower_shuffles =
      LIBCRUX_ML_KEM_VECTOR_REJ_SAMPLE_TABLE_REJECTION_SAMPLE_SHUFFLE_TABLE
          .data[(size_t)good.data[0U]];
  __m128i lower_shuffles0 = mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, &lower_shuffles, uint8_t));
  __m128i lower_coefficients = mm256_castsi256_si128(potential_coefficients);
  __m128i lower_coefficients0 =
      mm_shuffle_epi8(lower_coefficients, lower_shuffles0);
  mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8__count_ones(good.data[0U]);
  Eurydice_arr_88 upper_shuffles =
      LIBCRUX_ML_KEM_VECTOR_REJ_SAMPLE_TABLE_REJECTION_SAMPLE_SHUFFLE_TABLE
          .data[(size_t)good.data[1U]];
  __m128i upper_shuffles0 = mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, &upper_shuffles, uint8_t));
  __m128i upper_coefficients =
      mm256_extracti128_si256((int32_t)1, potential_coefficients, __m128i);
  __m128i upper_coefficients0 =
      mm_shuffle_epi8(upper_coefficients, upper_shuffles0);
  mm_storeu_si128(
      Eurydice_slice_subslice3(output, sampled_count,
                               sampled_count + (size_t)8U, int16_t *),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8__count_ones(good.data[1U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_rej_sample_f5(
    Eurydice_slice input, Eurydice_slice output) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, output);
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
inline __m256i libcrux_ml_kem_vector_avx2_clone_fd(__m256i *self) {
  return self[0U];
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
static Eurydice_arr_51 ZERO_d6_84(void) {
  Eurydice_arr_51 lit;
  __m256i repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_avx2_ZERO_f5(););
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(__m256i));
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
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_to_reduced_ring_element_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_12_f5(bytes);
    re.data[i0] = libcrux_ml_kem_vector_avx2_cond_subtract_3329_f5(coefficient);
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
    Eurydice_slice public_key, Eurydice_arr_260 *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    Eurydice_arr_51 uu____0 =
        deserialize_to_reduced_ring_element_84(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_e0(Eurydice_arr_84 *input) {
  Eurydice_arr_05 state = libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input->data, uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_41 with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_41_e0(Eurydice_arr_84 *input) {
  return shake128_init_absorb_final_e0(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_35
shake128_squeeze_first_three_blocks_e0(Eurydice_arr_05 *st) {
  Eurydice_arr_35 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  Eurydice_arr_b0 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_41 with
const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_35
shake128_squeeze_first_three_blocks_41_e0(Eurydice_arr_05 *self) {
  return shake128_squeeze_first_three_blocks_e0(self);
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
    Eurydice_arr_35 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_d6
shake128_squeeze_next_block_e0(Eurydice_arr_05 *st) {
  Eurydice_arr_d6 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_41 with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_d6
shake128_squeeze_next_block_41_e0(Eurydice_arr_05 *self) {
  return shake128_squeeze_next_block_e0(self);
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
    Eurydice_arr_d6 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static Eurydice_arr_51 ZERO_84(void) {
  Eurydice_arr_51 lit;
  __m256i repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_avx2_ZERO_f5(););
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51 from_i16_array_84(Eurydice_slice a) {
  Eurydice_arr_51 result = ZERO_84();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.data[i0] =
        libcrux_ml_kem_vector_avx2_from_i16_array_f5(Eurydice_slice_subslice3(
            a, i0 * (size_t)16U, (i0 + (size_t)1U) * (size_t)16U, int16_t *));
  }
  return result;
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
static KRML_MUSTINLINE Eurydice_arr_51 from_i16_array_d6_84(Eurydice_slice a) {
  return from_i16_array_84(a);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static Eurydice_arr_51 call_mut_e7_6c1(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_260
sample_from_xof_6c1(Eurydice_arr_84 *seeds) {
  Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_d4 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_05 xof_state = shake128_init_absorb_final_41_e0(seeds);
  Eurydice_arr_35 randomness0 =
      shake128_squeeze_first_three_blocks_41_e0(&xof_state);
  bool done = sample_from_uniform_distribution_next_ed(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_d6 randomness =
          shake128_squeeze_next_block_41_e0(&xof_state);
      done = sample_from_uniform_distribution_next_ed0(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_260 arr_mapped_str;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_6c1(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_6c1(Eurydice_arr_aa0 *A_transpose,
                                                Eurydice_arr_48 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_84 seeds; Eurydice_arr_48 repeat_expression[3U];
      KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)3U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_260 sampled = sample_from_xof_6c1(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)3U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_41
with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_41_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_H(input);
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
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_fb1(
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_ab(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_aa0 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_6c1(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_41_e0(Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 *
libcrux_ml_kem_ind_cca_unpacked_public_key_11_ab(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_91
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
clone_91_ab(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 *self) {
  Eurydice_arr_260 uu____0 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)3U, &self->t_as_ntt, Eurydice_arr_51, Eurydice_arr_260);
  Eurydice_arr_60 uu____1 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->seed_for_A, uint8_t, Eurydice_arr_60);
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63){
          .t_as_ntt = uu____0,
          .seed_for_A = uu____1,
          .A = core_array__core__clone__Clone_for__Array_T__N___clone(
              (size_t)3U, &self->A, Eurydice_arr_260, Eurydice_arr_aa0)});
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_d7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63
libcrux_ml_kem_ind_cca_unpacked_clone_d7_ab(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 *self) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 uu____0 =
      clone_91_ab(&self->ind_cpa_public_key);
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63){
      .ind_cpa_public_key = uu____0,
      .public_key_hash = core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->public_key_hash, uint8_t, Eurydice_arr_60)});
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i to_unsigned_field_modulus_84(__m256i a) {
  return libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_cc
serialize_uncompressed_ring_element_84(Eurydice_arr_51 *re) {
  Eurydice_arr_cc serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = to_unsigned_field_modulus_84(re->data[i0]);
    Eurydice_arr_6d bytes =
        libcrux_ml_kem_vector_avx2_serialize_12_f5(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)24U * i0,
                                    (size_t)24U * i0 + (size_t)24U, uint8_t *),
        Eurydice_array_to_slice((size_t)24U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
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
static KRML_MUSTINLINE void serialize_vector_ab(Eurydice_arr_260 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, key, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_84(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_260 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_74 *serialized) {
  serialize_vector_ab(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1184U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 *self,
    Eurydice_arr_74 *serialized) {
  serialize_public_key_mut_ed(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_ed(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    Eurydice_arr_74 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_ed(&self->public_key,
                                                       serialized);
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
static KRML_MUSTINLINE Eurydice_arr_74
serialize_public_key_ed(Eurydice_arr_260 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_74 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_ed(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE Eurydice_arr_74 serialized_dd_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 *self) {
  return libcrux_ml_kem_types_from_fd_d0(serialize_public_key_ed(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_74 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_ed(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  return serialized_dd_ed(&self->public_key);
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
serialize_unpacked_secret_key_ed(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 *public_key,
    Eurydice_arr_260 *private_key) {
  Eurydice_arr_74 public_key_serialized = serialize_public_key_ed(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_600 secret_key_serialized = {.data = {0U}};
  serialize_vector_ab(
      private_key,
      Eurydice_array_to_slice((size_t)1152U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair768){
      .fst = secret_key_serialized, .snd = public_key_serialized});
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_8c(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    Eurydice_arr_ea *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      serialize_unpacked_secret_key_ed(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_600 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_74 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      Eurydice_array_to_slice((size_t)1152U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_ea libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_8c(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  Eurydice_arr_ea sk = libcrux_ml_kem_types_default_d3_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_8c(self, &sk);
  return sk;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_to_uncompressed_ring_element_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    re.data[i0] = libcrux_ml_kem_vector_avx2_deserialize_12_f5(bytes);
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
    Eurydice_slice secret_key, Eurydice_arr_260 *secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          deserialize_to_uncompressed_ring_element_84(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static Eurydice_arr_51 call_mut_e7_b31(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_260
sample_from_xof_b31(Eurydice_arr_84 *seeds) {
  Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_d4 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_e4 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
          seeds);
  Eurydice_arr_35 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_ed(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_d6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
              &xof_state);
      done = sample_from_uniform_distribution_next_ed0(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_260 arr_mapped_str;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_b31(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_b31(Eurydice_arr_aa0 *A_transpose,
                                                Eurydice_arr_48 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_84 seeds; Eurydice_arr_48 repeat_expression[3U];
      KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)3U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_260 sampled = sample_from_xof_b31(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)3U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_bf1(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_ab(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_aa0 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_b31(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_2f(
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_ab(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_bf1(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1152U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static Eurydice_arr_260 default_70_ab(void) {
  Eurydice_arr_260 lit;
  Eurydice_arr_51 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_84(););
  memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_51));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 default_8b_ab(
    void) {
  Eurydice_arr_260 uu____0;
  Eurydice_arr_51 repeat_expression0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_84(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_51));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_260 repeat_expression1[3U];
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, Eurydice_arr_260 lit;
      Eurydice_arr_51 repeat_expression[3U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_84(););
      memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_51));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1,
         (size_t)3U * sizeof(Eurydice_arr_260));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63
libcrux_ml_kem_ind_cca_unpacked_default_30_ab(void) {
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63){
      .ind_cpa_public_key = default_8b_ab(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_ab(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63 uu____0 = {
      .ind_cpa_private_key = default_70_ab(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_ab()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_41
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_41_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_be(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  return G_41_e0(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_41(Eurydice_arr_46 *input) {
  Eurydice_arr_db out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  Eurydice_arr_d1 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_41
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_41_41(Eurydice_arr_46 *input) {
  return PRFxN_41(input);
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
static KRML_MUSTINLINE Eurydice_arr_51
sample_from_binomial_distribution_2_84(Eurydice_slice randomness) {
  Eurydice_arr_c1 sampled_i16s = {.data = {0U}};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t *);
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
    for (uint32_t i = 0U; i < core_num__u32__BITS / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      sampled_i16s.data[(size_t)8U * chunk_number + offset] =
          outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_84(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
sample_from_binomial_distribution_3_84(Eurydice_slice randomness) {
  Eurydice_arr_c1 sampled_i16s = {.data = {0U}};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)3U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)3U,
        chunk_number * (size_t)3U + (size_t)3U, uint8_t *);
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
      sampled_i16s.data[(size_t)4U * chunk_number + offset] =
          outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_84(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE Eurydice_arr_51
sample_from_binomial_distribution_89(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_84(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_84(Eurydice_arr_51 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    __m256i t = libcrux_ml_kem_vector_avx2_multiply_by_constant_f5(
        re->data[j + step], (int16_t)-1600);
    re->data[j + step] = libcrux_ml_kem_vector_avx2_sub_f5(re->data[j], &t);
    re->data[j] = libcrux_ml_kem_vector_avx2_add_f5(re->data[j], &t);
  }
}

typedef struct libcrux_ml_kem_vector_avx2_SIMD256Vector_x2_s {
  __m256i fst;
  __m256i snd;
} libcrux_ml_kem_vector_avx2_SIMD256Vector_x2;

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
ntt_layer_int_vec_step_84(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i t =
      libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(b, zeta_r);
  b = libcrux_ml_kem_vector_avx2_sub_f5(a, &t);
  a = libcrux_ml_kem_vector_avx2_add_f5(a, &t);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                     .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_84(size_t *zeta_i,
                                                   Eurydice_arr_51 *re,
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
          ntt_layer_int_vec_step_84(re->data[j], re->data[j + step_vec],
                                    libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      __m256i x = uu____0.fst;
      __m256i y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_84(size_t *zeta_i,
                                              Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_ntt_layer_3_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_84(size_t *zeta_i,
                                              Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_ntt_layer_2_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_84(size_t *zeta_i,
                                              Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_ntt_layer_1_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void poly_barrett_reduce_84(Eurydice_arr_51 *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    myself->data[i0] =
        libcrux_ml_kem_vector_avx2_barrett_reduce_f5(myself->data[i0]);
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
static KRML_MUSTINLINE void poly_barrett_reduce_d6_84(Eurydice_arr_51 *self) {
  poly_barrett_reduce_84(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_84(
    Eurydice_arr_51 *re) {
  ntt_at_layer_7_84(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_84(&zeta_i, re);
  ntt_at_layer_2_84(&zeta_i, re);
  ntt_at_layer_1_84(&zeta_i, re);
  poly_barrett_reduce_d6_84(re);
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
    Eurydice_arr_260 *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_db prf_outputs = PRFxN_41_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_89(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_84(&re_as_ntt->data[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_51 call_mut_73_221(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_51 ntt_multiply_84(Eurydice_arr_51 *myself,
                                                       Eurydice_arr_51 *rhs) {
  Eurydice_arr_51 out = ZERO_84();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    out.data[i0] = libcrux_ml_kem_vector_avx2_ntt_multiply_f5(
        &myself->data[i0], &rhs->data[i0],
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
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
ntt_multiply_d6_84(Eurydice_arr_51 *self, Eurydice_arr_51 *rhs) {
  return ntt_multiply_84(self, rhs);
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
static KRML_MUSTINLINE void add_to_ring_element_ab(Eurydice_arr_51 *myself,
                                                   Eurydice_arr_51 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, __m256i), __m256i);
       i++) {
    size_t i0 = i;
    myself->data[i0] =
        libcrux_ml_kem_vector_avx2_add_f5(myself->data[i0], &rhs->data[i0]);
  }
}

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
static KRML_MUSTINLINE void add_to_ring_element_d6_ab(Eurydice_arr_51 *self,
                                                      Eurydice_arr_51 *rhs) {
  add_to_ring_element_ab(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE __m256i to_standard_domain_84(__m256i vector) {
  return libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
      vector,
      LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_84(
    Eurydice_arr_51 *myself, Eurydice_arr_51 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form = to_standard_domain_84(myself->data[j]);
    __m256i sum = libcrux_ml_kem_vector_avx2_add_f5(coefficient_normal_form,
                                                    &error->data[j]);
    __m256i red = libcrux_ml_kem_vector_avx2_barrett_reduce_f5(sum);
    myself->data[j] = red;
  }
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
static KRML_MUSTINLINE void add_standard_error_reduce_d6_84(
    Eurydice_arr_51 *self, Eurydice_arr_51 *error) {
  add_standard_error_reduce_84(self, error);
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
    Eurydice_arr_260 *t_as_ntt, Eurydice_arr_aa0 *matrix_A,
    Eurydice_arr_260 *s_as_ntt, Eurydice_arr_260 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, matrix_A, Eurydice_arr_260),
               Eurydice_arr_260);
       i++) {
    size_t i0 = i;
    Eurydice_arr_260 *row = &matrix_A->data[i0];
    Eurydice_arr_51 uu____0 = ZERO_d6_84();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_51),
                  Eurydice_arr_51);
         i1++) {
      size_t j = i1;
      Eurydice_arr_51 *matrix_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_ab(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_84(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
    Eurydice_slice key_generation_seed, Eurydice_arr_260 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_be(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_aa0 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_6c1(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b41(private_key, &prf_input, 0U);
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_221(&lvalue););
  Eurydice_arr_260 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_b41(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_ab(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
static Eurydice_arr_51 call_mut_b4_ab(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
static Eurydice_arr_260 call_mut_7b_ab(void **_) {
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_ab(&lvalue););
  return arr_struct;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static inline Eurydice_arr_51 clone_c1_84(Eurydice_arr_51 *self) {
  return core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)16U, self, __m256i, Eurydice_arr_51);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static Eurydice_arr_aa0 transpose_a_ab(Eurydice_arr_aa0 ind_cpa_a) {
  Eurydice_arr_aa0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_ab(&lvalue););
  Eurydice_arr_aa0 A = arr_struct;
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          Eurydice_arr_51 uu____0 = clone_c1_84(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
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
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_bb1(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_221(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_aa0 A = transpose_a_ab(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_74 pk_serialized = serialize_public_key_ed(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_41_e0(Eurydice_array_to_slice((size_t)1184U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_be(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_41_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$3size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_880_s {
  Eurydice_arr_260 fst;
  Eurydice_arr_51 snd;
} tuple_880;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
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
static Eurydice_arr_51 call_mut_f1_481(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
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
static Eurydice_arr_51 call_mut_dd_481(void **_) { return ZERO_d6_84(); }

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
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_260 *error_1) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_db prf_outputs = PRFxN_41_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          sample_from_binomial_distribution_89(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_a6(Eurydice_slice input) {
  Eurydice_arr_d1 digest = {.data = {0U}};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, &digest, uint8_t), input);
  return digest;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_41_410(Eurydice_slice input) {
  return PRF_a6(input);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static Eurydice_arr_51 call_mut_a8_ab(void **_) { return ZERO_d6_84(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_84(size_t *zeta_i,
                                                     Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void invert_ntt_at_layer_2_84(size_t *zeta_i,
                                                     Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_84(size_t *zeta_i,
                                                     Eurydice_arr_51 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_f5(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U])););
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_avx2_SIMD256Vector_x2
inv_ntt_layer_int_vec_step_reduce_84(__m256i a, __m256i b, int16_t zeta_r) {
  __m256i a_minus_b = libcrux_ml_kem_vector_avx2_sub_f5(b, &a);
  a = libcrux_ml_kem_vector_avx2_barrett_reduce_f5(
      libcrux_ml_kem_vector_avx2_add_f5(a, &b));
  b = libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(a_minus_b,
                                                                    zeta_r);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_avx2_SIMD256Vector_x2){.fst = a,
                                                                     .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_84(size_t *zeta_i,
                                                          Eurydice_arr_51 *re,
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
          inv_ntt_layer_int_vec_step_reduce_84(
              re->data[j], re->data[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      __m256i x = uu____0.fst;
      __m256i y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_ab(Eurydice_arr_51 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_84(&zeta_i, re);
  invert_ntt_at_layer_2_84(&zeta_i, re);
  invert_ntt_at_layer_3_84(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_84(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_84(Eurydice_arr_51 *myself,
                                                Eurydice_arr_51 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
            myself->data[j], (int16_t)1441);
    __m256i sum = libcrux_ml_kem_vector_avx2_add_f5(coefficient_normal_form,
                                                    &error->data[j]);
    __m256i red = libcrux_ml_kem_vector_avx2_barrett_reduce_f5(sum);
    myself->data[j] = red;
  }
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
static KRML_MUSTINLINE void add_error_reduce_d6_84(Eurydice_arr_51 *self,
                                                   Eurydice_arr_51 *error) {
  add_error_reduce_84(self, error);
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
static KRML_MUSTINLINE Eurydice_arr_260
compute_vector_u_ab(Eurydice_arr_aa0 *a_as_ntt, Eurydice_arr_260 *r_as_ntt,
                    Eurydice_arr_260 *error_1) {
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_ab(&lvalue););
  Eurydice_arr_260 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)3U, a_as_ntt, Eurydice_arr_260),
                Eurydice_arr_260);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_260 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_51),
                 Eurydice_arr_51);
         i++) {
      size_t j = i;
      Eurydice_arr_51 *a_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_ab(&result.data[i1], &product);
    }
    invert_ntt_montgomery_ab(&result.data[i1]);
    add_error_reduce_d6_84(&result.data[i1], &error_1->data[i1]);
  }
  return result;
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i compress_f5_ef(__m256i vector) {
  return compress_ef(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_10_0e(Eurydice_arr_51 *re) {
  Eurydice_arr_b7 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_f5_ef(to_unsigned_field_modulus_84(re->data[i0]));
    Eurydice_arr_dc bytes =
        libcrux_ml_kem_vector_avx2_serialize_10_f5(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)20U * i0,
                                    (size_t)20U * i0 + (size_t)20U, uint8_t *),
        Eurydice_array_to_slice((size_t)20U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i compress_f5_c4(__m256i vector) {
  return compress_c4(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_ring_element_u_a4(Eurydice_arr_51 *re) {
  return compress_then_serialize_10_0e(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_8c(Eurydice_arr_260 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, &input, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_a4(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_880 encrypt_c1_481(Eurydice_slice randomness,
                                                Eurydice_arr_aa0 *matrix,
                                                Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_260 arr_struct0;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_481(&lvalue););
  Eurydice_arr_260 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b41(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_481(&lvalue););
  Eurydice_arr_260 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_b41(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_41_410(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_51 error_2 = sample_from_binomial_distribution_89(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_260 u = compute_vector_u_ab(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_8c(u, ciphertext);
  return (KRML_CLITERAL(tuple_880){.fst = r_as_ntt, .snd = error_2});
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_message_84(Eurydice_arr_60 *serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
                   __m256i coefficient_compressed =
                       libcrux_ml_kem_vector_avx2_deserialize_1_f5(
                           Eurydice_array_to_subslice3(
                               serialized, (size_t)2U * i0,
                               (size_t)2U * i0 + (size_t)2U, uint8_t *));
                   re.data[i0] = libcrux_ml_kem_vector_avx2_decompress_1_f5(
                       coefficient_compressed););
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51 add_message_error_reduce_84(
    Eurydice_arr_51 *myself, Eurydice_arr_51 *message, Eurydice_arr_51 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
            result.data[i0], (int16_t)1441);
    __m256i sum1 =
        libcrux_ml_kem_vector_avx2_add_f5(myself->data[i0], &message->data[i0]);
    __m256i sum2 =
        libcrux_ml_kem_vector_avx2_add_f5(coefficient_normal_form, &sum1);
    __m256i red = libcrux_ml_kem_vector_avx2_barrett_reduce_f5(sum2);
    result.data[i0] = red;
  }
  return result;
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
static KRML_MUSTINLINE Eurydice_arr_51 add_message_error_reduce_d6_84(
    Eurydice_arr_51 *self, Eurydice_arr_51 *message, Eurydice_arr_51 result) {
  return add_message_error_reduce_84(self, message, result);
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
static KRML_MUSTINLINE Eurydice_arr_51 compute_ring_element_v_ab(
    Eurydice_arr_260 *t_as_ntt, Eurydice_arr_260 *r_as_ntt,
    Eurydice_arr_51 *error_2, Eurydice_arr_51 *message) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_ab(&result, &product););
  invert_ntt_montgomery_ab(&result);
  return add_message_error_reduce_d6_84(error_2, message, result);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i compress_f5_d1(__m256i vector) {
  return compress_d1(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_84(
    Eurydice_arr_51 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient =
        compress_f5_d1(to_unsigned_field_modulus_84(re.data[i0]));
    Eurydice_arr_c4 bytes =
        libcrux_ml_kem_vector_avx2_serialize_4_f5(coefficient);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *),
        Eurydice_array_to_slice((size_t)8U, &bytes, uint8_t), uint8_t);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i compress_f5_f4(__m256i vector) {
  return compress_f4(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_84(
    Eurydice_arr_51 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficients = compress_f5_f4(
        libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(re.data[i0]));
    Eurydice_arr_77 bytes =
        libcrux_ml_kem_vector_avx2_serialize_5_f5(coefficients);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t *),
        Eurydice_array_to_slice((size_t)10U, &bytes, uint8_t), uint8_t);
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
    Eurydice_arr_51 re, Eurydice_slice out) {
  compress_then_serialize_4_84(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_ed(Eurydice_arr_260 *t_as_ntt,
                                          Eurydice_arr_260 *r_as_ntt,
                                          Eurydice_arr_51 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_51 message_as_ring_element =
      deserialize_then_decompress_message_84(message);
  Eurydice_arr_51 v = compute_ring_element_v_ab(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_unpacked_741(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_2c ciphertext = {.data = {0U}};
  tuple_880 uu____0 =
      encrypt_c1_481(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)960U, uint8_t *));
  Eurydice_arr_260 r_as_ntt = uu____0.fst;
  Eurydice_arr_51 error_2 = uu____0.snd;
  Eurydice_arr_260 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_260 *uu____2 = &r_as_ntt;
  Eurydice_arr_51 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_ed(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1088U, &ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
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
tuple_56 libcrux_ml_kem_ind_cca_unpacked_encapsulate_701(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_be(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_2c ciphertext = encrypt_unpacked_741(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_56){
      .fst = libcrux_ml_kem_types_from_e0_80(ciphertext),
      .snd = shared_secret_array});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static Eurydice_arr_51 call_mut_35_ed(void **_) { return ZERO_d6_84(); }

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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_f5_ef(__m256i vector) {
  return decompress_ciphertext_coefficient_ef(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_10_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_10_f5(bytes);
    re.data[i0] = decompress_ciphertext_coefficient_f5_ef(coefficient);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_f5_c4(__m256i vector) {
  return decompress_ciphertext_coefficient_c4(vector);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_11_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)22U,
                                 i0 * (size_t)22U + (size_t)22U, uint8_t *);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_11_f5(bytes);
    re.data[i0] = decompress_ciphertext_coefficient_f5_c4(coefficient);
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_ring_element_u_ee(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_84(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_ee(Eurydice_arr_51 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_84(&zeta_i, re);
  ntt_at_layer_2_84(&zeta_i, re);
  ntt_at_layer_1_84(&zeta_i, re);
  poly_barrett_reduce_d6_84(re);
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
static KRML_MUSTINLINE Eurydice_arr_260
deserialize_then_decompress_u_ed(Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_ed(&lvalue););
  Eurydice_arr_260 u_as_ntt = arr_struct;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_ee(u_bytes);
    ntt_vector_u_ee(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_f5_d1(__m256i vector) {
  return decompress_ciphertext_coefficient_d1(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_4_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    __m256i coefficient = libcrux_ml_kem_vector_avx2_deserialize_4_f5(bytes);
    re.data[i0] = decompress_ciphertext_coefficient_f5_d1(coefficient);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE __m256i
decompress_ciphertext_coefficient_f5_f4(__m256i vector) {
  return decompress_ciphertext_coefficient_f4(vector);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_5_84(Eurydice_slice serialized) {
  Eurydice_arr_51 re = ZERO_d6_84();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)10U,
                                 i0 * (size_t)10U + (size_t)10U, uint8_t *);
    re.data[i0] = libcrux_ml_kem_vector_avx2_deserialize_5_f5(bytes);
    re.data[i0] = decompress_ciphertext_coefficient_f5_f4(re.data[i0]);
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
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_ring_element_v_ed(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_84(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_51
subtract_reduce_84(Eurydice_arr_51 *myself, Eurydice_arr_51 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient_normal_form =
        libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
            b.data[i0], (int16_t)1441);
    __m256i diff = libcrux_ml_kem_vector_avx2_sub_f5(myself->data[i0],
                                                     &coefficient_normal_form);
    __m256i red = libcrux_ml_kem_vector_avx2_barrett_reduce_f5(diff);
    b.data[i0] = red;
  }
  return b;
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
static KRML_MUSTINLINE Eurydice_arr_51
subtract_reduce_d6_84(Eurydice_arr_51 *self, Eurydice_arr_51 b) {
  return subtract_reduce_84(self, b);
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
static KRML_MUSTINLINE Eurydice_arr_51
compute_message_ab(Eurydice_arr_51 *v, Eurydice_arr_260 *secret_as_ntt,
                   Eurydice_arr_260 *u_as_ntt) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_ab(&result, &product););
  invert_ntt_montgomery_ab(&result);
  return subtract_reduce_d6_84(v, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_60
compress_then_serialize_message_84(Eurydice_arr_51 re) {
  Eurydice_arr_60 serialized = {.data = {0U}};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      __m256i coefficient = to_unsigned_field_modulus_84(re.data[i0]);
      __m256i coefficient_compressed =
          libcrux_ml_kem_vector_avx2_compress_1_f5(coefficient);
      Eurydice_arr_8b bytes =
          libcrux_ml_kem_vector_avx2_serialize_1_f5(coefficient_compressed);
      Eurydice_slice_copy(
          Eurydice_array_to_subslice3(&serialized, (size_t)2U * i0,
                                      (size_t)2U * i0 + (size_t)2U, uint8_t *),
          Eurydice_array_to_slice((size_t)2U, &bytes, uint8_t), uint8_t););
  return serialized;
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_2f(Eurydice_arr_260 *secret_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_260 u_as_ntt = deserialize_then_decompress_u_ed(ciphertext);
  Eurydice_arr_51 v = deserialize_then_decompress_ring_element_v_ed(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_51 message = compute_message_ab(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_84(message);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_9e(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, &digest, uint8_t), input);
  return digest;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 3
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_41_41(Eurydice_slice input) {
  return PRF_9e(input);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_121(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_2f(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_480 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_41_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext = encrypt_unpacked_741(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, &expected_ciphertext,
                                  uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
static Eurydice_arr_51 call_mut_0b_ab(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_260
deserialize_ring_elements_reduced_out_ab(Eurydice_slice public_key) {
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_ab(&lvalue););
  Eurydice_arr_260 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_ab(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_ed(
    Eurydice_arr_74 *public_key) {
  Eurydice_arr_260 deserialized_pk =
      deserialize_ring_elements_reduced_out_ab(Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_260 *uu____0 = &deserialized_pk;
  Eurydice_arr_74 public_key_serialized = serialize_public_key_ed(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)1184U, public_key, &public_key_serialized,
                           uint8_t);
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
    Eurydice_arr_ea *private_key) {
  Eurydice_arr_60 t = H_41_e0(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)3U,
      (size_t)768U * (size_t)3U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_ae(private_key);
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
  Eurydice_arr_260 private_key = default_70_ab();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 public_key =
      default_8b_ab();
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_ea *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_ea *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_ea *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_e0(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_ea *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE Eurydice_arr_ea serialize_kem_secret_key_ae(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_ea out = {.data = {0U}};
  serialize_kem_secret_key_mut_ae(private_key, public_key,
                                  implicit_rejection_value, &out);
  return out;
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
libcrux_ml_kem_ind_cca_generate_keypair_bb1(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_5d1(ind_cpa_keypair_randomness);
  Eurydice_arr_600 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_74 public_key = uu____0.snd;
  Eurydice_arr_ea secret_key_serialized = serialize_kem_secret_key_ae(
      Eurydice_array_to_slice((size_t)1152U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_ea private_key =
      libcrux_ml_kem_types_from_77_28(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_74(
      private_key, libcrux_ml_kem_types_from_fd_d0(public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_be(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_ab(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_aa0 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_6c1(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
    build_unpacked_public_key_fa1(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
      unpacked_public_key = default_8b_ab();
  build_unpacked_public_key_mut_fa1(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_741(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63
      unpacked_public_key = build_unpacked_public_key_fa1(public_key);
  return encrypt_unpacked_741(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_ae(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_56 libcrux_ml_kem_ind_cca_encapsulate_701(Eurydice_arr_74 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_be(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_e0(Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_2c ciphertext =
      encrypt_741(Eurydice_array_to_slice(
                      (size_t)1184U,
                      libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_2c uu____2 = libcrux_ml_kem_types_from_e0_80(ciphertext);
  return (
      KRML_CLITERAL(tuple_56){.fst = uu____2, .snd = kdf_39_ae(shared_secret)});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static Eurydice_arr_51 call_mut_0b_2f(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_2f(Eurydice_slice secret_key,
                                                  Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_260 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_2f(&lvalue););
  Eurydice_arr_260 secret_key_unpacked = arr_struct;
  deserialize_vector_ab(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_2f(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_a11(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_2f(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_480 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_41_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext =
      encrypt_741(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_ae(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_ae(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
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
    Eurydice_slice public_key, Eurydice_arr_4c *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    Eurydice_arr_51 uu____0 =
        deserialize_to_reduced_ring_element_84(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_ac(Eurydice_arr_78 *input) {
  Eurydice_arr_05 state = libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[3U], uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_41 with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_41_ac(Eurydice_arr_78 *input) {
  return shake128_init_absorb_final_ac(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_ec
shake128_squeeze_first_three_blocks_ac(Eurydice_arr_05 *st) {
  Eurydice_arr_ec out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  Eurydice_arr_b0 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  out.data[3U] = out3;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_41 with
const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_ec
shake128_squeeze_first_three_blocks_41_ac(Eurydice_arr_05 *self) {
  return shake128_squeeze_first_three_blocks_ac(self);
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
    Eurydice_arr_ec *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_a6
shake128_squeeze_next_block_ac(Eurydice_arr_05 *st) {
  Eurydice_arr_a6 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  out.data[3U] = out3;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_41 with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_a6
shake128_squeeze_next_block_41_ac(Eurydice_arr_05 *self) {
  return shake128_squeeze_next_block_ac(self);
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
    Eurydice_arr_a6 *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static Eurydice_arr_51 call_mut_e7_6c0(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_4c
sample_from_xof_6c0(Eurydice_arr_78 *seeds) {
  Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8a out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_05 xof_state = shake128_init_absorb_final_41_ac(seeds);
  Eurydice_arr_ec randomness0 =
      shake128_squeeze_first_three_blocks_41_ac(&xof_state);
  bool done = sample_from_uniform_distribution_next_78(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a6 randomness =
          shake128_squeeze_next_block_41_ac(&xof_state);
      done = sample_from_uniform_distribution_next_780(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_4c arr_mapped_str;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_6c0(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_6c0(Eurydice_arr_95 *A_transpose,
                                                Eurydice_arr_48 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_78 seeds; Eurydice_arr_48 repeat_expression[4U];
      KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)4U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_4c sampled = sample_from_xof_6c0(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)4U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_41
with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_41_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_H(input);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash,
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_fb0(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1568U, public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_42(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_95 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_6c0(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_41_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
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
static KRML_MUSTINLINE void serialize_vector_42(Eurydice_arr_4c *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, key, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_84(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_4c *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_00 *serialized) {
  serialize_vector_42(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1568U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_78(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *self,
    Eurydice_arr_00 *serialized) {
  serialize_public_key_mut_78(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_78(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *self,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_78(&self->public_key,
                                                       serialized);
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
static KRML_MUSTINLINE Eurydice_arr_00
serialize_public_key_78(Eurydice_arr_4c *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_00 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_78(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE Eurydice_arr_00 serialized_dd_78(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *self) {
  return libcrux_ml_kem_types_from_fd_af(serialize_public_key_78(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_00 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_78(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *self) {
  return serialized_dd_78(&self->public_key);
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
serialize_unpacked_secret_key_1e(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_4c *private_key) {
  Eurydice_arr_00 public_key_serialized = serialize_public_key_78(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_38 secret_key_serialized = {.data = {0U}};
  serialize_vector_42(
      private_key,
      Eurydice_array_to_slice((size_t)1536U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair1024){
      .fst = secret_key_serialized, .snd = public_key_serialized});
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_c9(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *self,
    Eurydice_arr_17 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      serialize_unpacked_secret_key_1e(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_38 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_00 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
      Eurydice_array_to_slice((size_t)1536U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_17 libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_c9(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *self) {
  Eurydice_arr_17 sk = libcrux_ml_kem_types_default_d3_39();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_c9(self, &sk);
  return sk;
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
    Eurydice_slice secret_key, Eurydice_arr_4c *secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          deserialize_to_uncompressed_ring_element_84(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static Eurydice_arr_51 call_mut_e7_b30(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_4c
sample_from_xof_b30(Eurydice_arr_78 *seeds) {
  Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8a out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_180 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
          seeds);
  Eurydice_arr_ec randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_78(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
              &xof_state);
      done = sample_from_uniform_distribution_next_780(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_4c arr_mapped_str;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_b30(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_b30(Eurydice_arr_95 *A_transpose,
                                                Eurydice_arr_48 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_78 seeds; Eurydice_arr_48 repeat_expression[4U];
      KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)4U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_4c sampled = sample_from_xof_b30(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)4U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_bf0(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_42(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_95 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_b30(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_37(
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_42(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_bf0(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1536U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static Eurydice_arr_4c default_70_42(void) {
  Eurydice_arr_4c lit;
  Eurydice_arr_51 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_84(););
  memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_51));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 default_8b_42(
    void) {
  Eurydice_arr_4c uu____0;
  Eurydice_arr_51 repeat_expression0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_84(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_51));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_4c repeat_expression1[4U];
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, Eurydice_arr_4c lit;
      Eurydice_arr_51 repeat_expression[4U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_84(););
      memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_51));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1, (size_t)4U * sizeof(Eurydice_arr_4c));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
libcrux_ml_kem_ind_cca_unpacked_default_30_42(void) {
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39){
      .ind_cpa_public_key = default_8b_42(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_42(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_39 uu____0 = {
      .ind_cpa_private_key = default_70_42(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_42()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_41
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_41_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_6a(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  return G_41_ac(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_44(Eurydice_arr_65 *input) {
  Eurydice_arr_cc0 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  Eurydice_arr_d1 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[3U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  out.data[3U] = out3;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_41
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_41_44(Eurydice_arr_65 *input) {
  return PRFxN_44(input);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b40(
    Eurydice_arr_4c *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_cc0 prf_outputs = PRFxN_41_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_89(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_84(&re_as_ntt->data[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_51 call_mut_73_220(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE void add_to_ring_element_42(Eurydice_arr_51 *myself,
                                                   Eurydice_arr_51 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, __m256i), __m256i);
       i++) {
    size_t i0 = i;
    myself->data[i0] =
        libcrux_ml_kem_vector_avx2_add_f5(myself->data[i0], &rhs->data[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_42(Eurydice_arr_51 *self,
                                                      Eurydice_arr_51 *rhs) {
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
    Eurydice_arr_4c *t_as_ntt, Eurydice_arr_95 *matrix_A,
    Eurydice_arr_4c *s_as_ntt, Eurydice_arr_4c *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, matrix_A, Eurydice_arr_4c),
               Eurydice_arr_4c);
       i++) {
    size_t i0 = i;
    Eurydice_arr_4c *row = &matrix_A->data[i0];
    Eurydice_arr_51 uu____0 = ZERO_d6_84();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_51),
                  Eurydice_arr_51);
         i1++) {
      size_t j = i1;
      Eurydice_arr_51 *matrix_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_42(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_84(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
static KRML_MUSTINLINE void generate_keypair_unpacked_220(
    Eurydice_slice key_generation_seed, Eurydice_arr_4c *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_6a(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_95 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_6c0(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b40(private_key, &prf_input, 0U);
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_220(&lvalue););
  Eurydice_arr_4c error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_b40(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_42(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
static Eurydice_arr_51 call_mut_b4_42(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
static Eurydice_arr_4c call_mut_7b_42(void **_) {
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_42(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static Eurydice_arr_95 transpose_a_42(Eurydice_arr_95 ind_cpa_a) {
  Eurydice_arr_95 arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_42(&lvalue););
  Eurydice_arr_95 A = arr_struct;
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          Eurydice_arr_51 uu____0 = clone_c1_84(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
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
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_bb0(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_220(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_95 A = transpose_a_42(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_00 pk_serialized = serialize_public_key_78(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_41_ac(Eurydice_array_to_slice((size_t)1568U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_6a(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_41_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$4size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_0c_s {
  Eurydice_arr_4c fst;
  Eurydice_arr_51 snd;
} tuple_0c;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
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
static Eurydice_arr_51 call_mut_f1_480(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
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
static Eurydice_arr_51 call_mut_dd_480(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b40(
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_4c *error_1) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_cc0 prf_outputs = PRFxN_41_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          sample_from_binomial_distribution_89(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_41_440(Eurydice_slice input) {
  return PRF_a6(input);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static Eurydice_arr_51 call_mut_a8_42(void **_) { return ZERO_d6_84(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_42(Eurydice_arr_51 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_84(&zeta_i, re);
  invert_ntt_at_layer_2_84(&zeta_i, re);
  invert_ntt_at_layer_3_84(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_84(re);
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
static KRML_MUSTINLINE Eurydice_arr_4c
compute_vector_u_42(Eurydice_arr_95 *a_as_ntt, Eurydice_arr_4c *r_as_ntt,
                    Eurydice_arr_4c *error_1) {
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_42(&lvalue););
  Eurydice_arr_4c result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)4U, a_as_ntt, Eurydice_arr_4c),
                Eurydice_arr_4c);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_4c *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_51),
                 Eurydice_arr_51);
         i++) {
      size_t j = i;
      Eurydice_arr_51 *a_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_42(&result.data[i1], &product);
    }
    invert_ntt_montgomery_42(&result.data[i1]);
    add_error_reduce_d6_84(&result.data[i1], &error_1->data[i1]);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_11_0e0(Eurydice_arr_51 *re) {
  Eurydice_arr_79 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    __m256i coefficient = compress_f5_c4(
        libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(re->data[i0]));
    Eurydice_arr_f3 bytes =
        libcrux_ml_kem_vector_avx2_serialize_11_f5(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)22U * i0,
                                    (size_t)22U * i0 + (size_t)22U, uint8_t *),
        Eurydice_array_to_slice((size_t)22U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_ring_element_u_6f(Eurydice_arr_51 *re) {
  return compress_then_serialize_11_0e0(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_c9(Eurydice_arr_4c input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, &input, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_79 lvalue = compress_then_serialize_ring_element_u_6f(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)352U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_0c encrypt_c1_480(Eurydice_slice randomness,
                                               Eurydice_arr_95 *matrix,
                                               Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_4c arr_struct0;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_480(&lvalue););
  Eurydice_arr_4c r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b40(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_480(&lvalue););
  Eurydice_arr_4c error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_b40(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_41_440(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_51 error_2 = sample_from_binomial_distribution_89(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_4c u = compute_vector_u_42(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_c9(u, ciphertext);
  return (KRML_CLITERAL(tuple_0c){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_51
compute_ring_element_v_42(Eurydice_arr_4c *t_as_ntt, Eurydice_arr_4c *r_as_ntt,
                          Eurydice_arr_51 *error_2, Eurydice_arr_51 *message) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_42(&result, &product););
  invert_ntt_montgomery_42(&result);
  return add_message_error_reduce_d6_84(error_2, message, result);
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
    Eurydice_arr_51 re, Eurydice_slice out) {
  compress_then_serialize_5_84(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_1e(Eurydice_arr_4c *t_as_ntt,
                                          Eurydice_arr_4c *r_as_ntt,
                                          Eurydice_arr_51 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_51 message_as_ring_element =
      deserialize_then_decompress_message_84(message);
  Eurydice_arr_51 v = compute_ring_element_v_42(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_unpacked_740(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_00 ciphertext = {.data = {0U}};
  tuple_0c uu____0 =
      encrypt_c1_480(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)1408U, uint8_t *));
  Eurydice_arr_4c r_as_ntt = uu____0.fst;
  Eurydice_arr_51 error_2 = uu____0.snd;
  Eurydice_arr_4c *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_4c *uu____2 = &r_as_ntt;
  Eurydice_arr_51 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_1e(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1568U, &ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
tuple_2b libcrux_ml_kem_ind_cca_unpacked_encapsulate_700(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_6a(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_00 ciphertext = encrypt_unpacked_740(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_2b){
      .fst = libcrux_ml_kem_types_from_e0_af(ciphertext),
      .snd = shared_secret_array});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static Eurydice_arr_51 call_mut_35_1e(void **_) { return ZERO_d6_84(); }

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_ring_element_u_85(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_84(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_85(Eurydice_arr_51 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_84(&zeta_i, re);
  ntt_at_layer_2_84(&zeta_i, re);
  ntt_at_layer_1_84(&zeta_i, re);
  poly_barrett_reduce_d6_84(re);
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
static KRML_MUSTINLINE Eurydice_arr_4c
deserialize_then_decompress_u_1e(Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_1e(&lvalue););
  Eurydice_arr_4c u_as_ntt = arr_struct;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U,
        uint8_t *);
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_85(u_bytes);
    ntt_vector_u_85(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_ring_element_v_78(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_84(serialized);
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
static KRML_MUSTINLINE Eurydice_arr_51
compute_message_42(Eurydice_arr_51 *v, Eurydice_arr_4c *secret_as_ntt,
                   Eurydice_arr_4c *u_as_ntt) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_42(&result, &product););
  invert_ntt_montgomery_42(&result);
  return subtract_reduce_d6_84(v, result);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_37(Eurydice_arr_4c *secret_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_4c u_as_ntt = deserialize_then_decompress_u_1e(ciphertext);
  Eurydice_arr_51 v = deserialize_then_decompress_ring_element_v_78(
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_51 message = compute_message_42(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_84(message);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 4
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_41_44(Eurydice_slice input) {
  return PRF_9e(input);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_120(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_37(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_e7 to_hash =
      libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_41_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext = encrypt_unpacked_740(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
          Eurydice_array_to_slice((size_t)1568U, &expected_ciphertext,
                                  uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 4
*/
static Eurydice_arr_51 call_mut_0b_42(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_4c
deserialize_ring_elements_reduced_out_42(Eurydice_slice public_key) {
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_42(&lvalue););
  Eurydice_arr_4c deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_42(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_78(
    Eurydice_arr_00 *public_key) {
  Eurydice_arr_4c deserialized_pk =
      deserialize_ring_elements_reduced_out_42(Eurydice_array_to_subslice_to(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_4c *uu____0 = &deserialized_pk;
  Eurydice_arr_00 public_key_serialized = serialize_public_key_78(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)1568U, public_key, &public_key_serialized,
                           uint8_t);
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
    Eurydice_arr_17 *private_key) {
  Eurydice_arr_60 t = H_41_ac(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)4U,
      (size_t)768U * (size_t)4U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)4U + (size_t)32U,
      (size_t)768U * (size_t)4U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_5e(private_key);
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
  Eurydice_arr_4c private_key = default_70_42();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39 public_key =
      default_8b_42();
  generate_keypair_unpacked_220(key_generation_seed, &private_key, &public_key);
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_17 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_17 *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_17 *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_ac(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_17 *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE Eurydice_arr_17 serialize_kem_secret_key_5e(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_17 out = {.data = {0U}};
  serialize_kem_secret_key_mut_5e(private_key, public_key,
                                  implicit_rejection_value, &out);
  return out;
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
libcrux_ml_kem_ind_cca_generate_keypair_bb0(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_5d0(ind_cpa_keypair_randomness);
  Eurydice_arr_38 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_00 public_key = uu____0.snd;
  Eurydice_arr_17 secret_key_serialized = serialize_kem_secret_key_5e(
      Eurydice_array_to_slice((size_t)1536U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_17 private_key =
      libcrux_ml_kem_types_from_77_39(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_94(
      private_key, libcrux_ml_kem_types_from_fd_af(public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_6a(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_42(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_95 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_6c0(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39
    build_unpacked_public_key_fa0(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39
      unpacked_public_key = default_8b_42();
  build_unpacked_public_key_mut_fa0(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_740(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_39
      unpacked_public_key = build_unpacked_public_key_fa0(public_key);
  return encrypt_unpacked_740(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_5e(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_2b libcrux_ml_kem_ind_cca_encapsulate_700(Eurydice_arr_00 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_6a(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_00 ciphertext =
      encrypt_740(Eurydice_array_to_slice(
                      (size_t)1568U,
                      libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_00 uu____2 = libcrux_ml_kem_types_from_e0_af(ciphertext);
  return (
      KRML_CLITERAL(tuple_2b){.fst = uu____2, .snd = kdf_39_5e(shared_secret)});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static Eurydice_arr_51 call_mut_0b_37(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_37(Eurydice_slice secret_key,
                                                  Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_4c arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_37(&lvalue););
  Eurydice_arr_4c secret_key_unpacked = arr_struct;
  deserialize_vector_42(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_37(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_a10(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_37(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_e7 to_hash =
      libcrux_ml_kem_utils_into_padded_array_7f(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_41_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext =
      encrypt_740(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_5e(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_5e(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
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
    Eurydice_slice public_key, Eurydice_arr_36 *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    Eurydice_arr_51 uu____0 =
        deserialize_to_reduced_ring_element_84(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_fd(Eurydice_arr_340 *input) {
  Eurydice_arr_05 state = libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
      &state, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, input->data, uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_init_absorb_final_41 with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_05
shake128_init_absorb_final_41_fd(Eurydice_arr_340 *input) {
  return shake128_init_absorb_final_fd(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_45
shake128_squeeze_first_three_blocks_fd(Eurydice_arr_05 *st) {
  Eurydice_arr_45 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  Eurydice_arr_b0 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_first_three_blocks_41 with
const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_45
shake128_squeeze_first_three_blocks_41_fd(Eurydice_arr_05 *self) {
  return shake128_squeeze_first_three_blocks_fd(self);
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
    Eurydice_arr_45 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_a9
shake128_squeeze_next_block_fd(Eurydice_arr_05 *st) {
  Eurydice_arr_a9 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.avx2.shake128_squeeze_next_block_41 with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_a9
shake128_squeeze_next_block_41_fd(Eurydice_arr_05 *self) {
  return shake128_squeeze_next_block_fd(self);
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
    Eurydice_arr_a9 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static Eurydice_arr_51 call_mut_e7_6c(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_36
sample_from_xof_6c(Eurydice_arr_340 *seeds) {
  Eurydice_arr_fb sampled_coefficients = {.data = {0U}};
  Eurydice_arr_04 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_05 xof_state = shake128_init_absorb_final_41_fd(seeds);
  Eurydice_arr_45 randomness0 =
      shake128_squeeze_first_three_blocks_41_fd(&xof_state);
  bool done = sample_from_uniform_distribution_next_29(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a9 randomness =
          shake128_squeeze_next_block_41_fd(&xof_state);
      done = sample_from_uniform_distribution_next_290(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_36 arr_mapped_str;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_6c(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_6c(Eurydice_arr_e20 *A_transpose,
                                               Eurydice_arr_48 *seed,
                                               bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_340 seeds; Eurydice_arr_48 repeat_expression[2U];
      KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)2U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_36 sampled = sample_from_xof_6c(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)2U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.H_41
with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_41_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_H(input);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash,
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_fb(
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_89(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 =
      libcrux_ml_kem_utils_into_padded_array_9e(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_e20 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue =
      libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  sample_matrix_A_6c(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_41_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
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
static KRML_MUSTINLINE void serialize_vector_89(Eurydice_arr_36 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, key, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_84(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_36 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_30 *serialized) {
  serialize_vector_89(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)800U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_29(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94 *self,
    Eurydice_arr_30 *serialized) {
  serialize_public_key_mut_29(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_29(
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *self,
    Eurydice_arr_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_29(&self->public_key,
                                                       serialized);
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
static KRML_MUSTINLINE Eurydice_arr_30
serialize_public_key_29(Eurydice_arr_36 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_30 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_29(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE Eurydice_arr_30 serialized_dd_29(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94 *self) {
  return libcrux_ml_kem_types_from_fd_4d(serialize_public_key_29(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_30 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_29(
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *self) {
  return serialized_dd_29(&self->public_key);
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
serialize_unpacked_secret_key_ba(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 *public_key,
    Eurydice_arr_36 *private_key) {
  Eurydice_arr_30 public_key_serialized = serialize_public_key_29(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_56 secret_key_serialized = {.data = {0U}};
  serialize_vector_89(
      private_key,
      Eurydice_array_to_slice((size_t)768U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair512){
      .fst = secret_key_serialized, .snd = public_key_serialized});
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2d(
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *self,
    Eurydice_arr_7f *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      serialize_unpacked_secret_key_ba(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_56 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_30 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
      Eurydice_array_to_slice((size_t)768U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_7f libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_2d(
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *self) {
  Eurydice_arr_7f sk = libcrux_ml_kem_types_default_d3_2a();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2d(self, &sk);
  return sk;
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
    Eurydice_slice secret_key, Eurydice_arr_36 *secret_as_ntt) {
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          deserialize_to_uncompressed_ring_element_84(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static Eurydice_arr_51 call_mut_e7_b3(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_84(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_36
sample_from_xof_b3(Eurydice_arr_340 *seeds) {
  Eurydice_arr_fb sampled_coefficients = {.data = {0U}};
  Eurydice_arr_04 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_73 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
          seeds);
  Eurydice_arr_45 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_29(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a9 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
              &xof_state);
      done = sample_from_uniform_distribution_next_290(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_36 arr_mapped_str;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_b3(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_b3(Eurydice_arr_e20 *A_transpose,
                                               Eurydice_arr_48 *seed,
                                               bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_340 seeds; Eurydice_arr_48 repeat_expression[2U];
      KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_48););
      memcpy(seeds.data, repeat_expression,
             (size_t)2U * sizeof(Eurydice_arr_48));
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_36 sampled = sample_from_xof_b3(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)2U, &sampled,
                                                          Eurydice_arr_51),
                                  Eurydice_arr_51);
           i++) {
        size_t j = i;
        Eurydice_arr_51 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_bf(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_89(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_e20 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_b3(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_4b(
    Eurydice_arr_7f *private_key,
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_89(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_bf(ind_cpa_public_key,
                                   &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)768U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static Eurydice_arr_36 default_70_89(void) {
  Eurydice_arr_36 lit;
  Eurydice_arr_51 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_84(););
  memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_51));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 default_8b_89(
    void) {
  Eurydice_arr_36 uu____0;
  Eurydice_arr_51 repeat_expression0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_84(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)2U * sizeof(Eurydice_arr_51));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_36 repeat_expression1[2U];
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, Eurydice_arr_36 lit;
      Eurydice_arr_51 repeat_expression[2U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_84(););
      memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_51));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1, (size_t)2U * sizeof(Eurydice_arr_36));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94
libcrux_ml_kem_ind_cca_unpacked_default_30_89(void) {
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94){
      .ind_cpa_public_key = default_8b_89(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_89(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_94 uu____0 = {
      .ind_cpa_private_key = default_70_89(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_89()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.G_41
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_41_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_f8(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)2U;
  return G_41_fd(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_49(Eurydice_arr_cf *input) {
  Eurydice_arr_a80 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_f2){
              .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_f2){
              .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_f2 out0 = {.data = {0U}};
  Eurydice_arr_f2 out1 = {.data = {0U}};
  Eurydice_arr_f2 out2 = {.data = {0U}};
  Eurydice_arr_f2 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_41
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_41_49(Eurydice_arr_cf *input) {
  return PRFxN_49(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE Eurydice_arr_51
sample_from_binomial_distribution_ab(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_84(randomness);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b4(
    Eurydice_arr_36 *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_cf prf_inputs;
  Eurydice_arr_3e repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)2U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(&prf_inputs, domain_separator);
  Eurydice_arr_a80 prf_outputs = PRFxN_41_49(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_ab(Eurydice_array_to_slice(
              (size_t)192U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_84(&re_as_ntt->data[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static Eurydice_arr_51 call_mut_73_22(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE void add_to_ring_element_89(Eurydice_arr_51 *myself,
                                                   Eurydice_arr_51 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, __m256i), __m256i);
       i++) {
    size_t i0 = i;
    myself->data[i0] =
        libcrux_ml_kem_vector_avx2_add_f5(myself->data[i0], &rhs->data[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_89(Eurydice_arr_51 *self,
                                                      Eurydice_arr_51 *rhs) {
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
    Eurydice_arr_36 *t_as_ntt, Eurydice_arr_e20 *matrix_A,
    Eurydice_arr_36 *s_as_ntt, Eurydice_arr_36 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, matrix_A, Eurydice_arr_36),
               Eurydice_arr_36);
       i++) {
    size_t i0 = i;
    Eurydice_arr_36 *row = &matrix_A->data[i0];
    Eurydice_arr_51 uu____0 = ZERO_d6_84();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_51),
                  Eurydice_arr_51);
         i1++) {
      size_t j = i1;
      Eurydice_arr_51 *matrix_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_89(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_84(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
static KRML_MUSTINLINE void generate_keypair_unpacked_22(
    Eurydice_slice key_generation_seed, Eurydice_arr_36 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_f8(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_e20 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_6c(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b4(private_key, &prf_input, 0U);
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_22(&lvalue););
  Eurydice_arr_36 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_b4(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_89(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
static Eurydice_arr_51 call_mut_b4_89(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
static Eurydice_arr_36 call_mut_7b_89(void **_) {
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_89(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static Eurydice_arr_e20 transpose_a_89(Eurydice_arr_e20 ind_cpa_a) {
  Eurydice_arr_e20 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_89(&lvalue););
  Eurydice_arr_e20 A = arr_struct;
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          Eurydice_arr_51 uu____0 = clone_c1_84(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
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
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_bb(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_22(ind_cpa_keypair_randomness,
                               &out->private_key.ind_cpa_private_key,
                               &out->public_key.ind_cpa_public_key);
  Eurydice_arr_e20 A = transpose_a_89(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_30 pk_serialized = serialize_public_key_29(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_41_fd(Eurydice_array_to_slice((size_t)800U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_f8(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_41_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector[[$2size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct tuple_71_s {
  Eurydice_arr_36 fst;
  Eurydice_arr_51 snd;
} tuple_71;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
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
static Eurydice_arr_51 call_mut_f1_48(void **_) { return ZERO_d6_84(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
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
static Eurydice_arr_51 call_mut_dd_48(void **_) { return ZERO_d6_84(); }

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_490(Eurydice_arr_cf *input) {
  Eurydice_arr_a01 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  Eurydice_arr_d1 out3 = {.data = {0U}};
  libcrux_sha3_avx2_x4_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRFxN_41
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_41_490(Eurydice_arr_cf *input) {
  return PRFxN_490(input);
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
static KRML_MUSTINLINE uint8_t
sample_ring_element_cbd_b4(Eurydice_arr_3e *prf_input, uint8_t domain_separator,
                           Eurydice_arr_36 *error_1) {
  Eurydice_arr_cf prf_inputs;
  Eurydice_arr_3e repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)2U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(&prf_inputs, domain_separator);
  Eurydice_arr_a01 prf_outputs = PRFxN_41_490(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_51 uu____0 =
          sample_from_binomial_distribution_89(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_41_490(Eurydice_slice input) {
  return PRF_a6(input);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static Eurydice_arr_51 call_mut_a8_89(void **_) { return ZERO_d6_84(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_89(Eurydice_arr_51 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_84(&zeta_i, re);
  invert_ntt_at_layer_2_84(&zeta_i, re);
  invert_ntt_at_layer_3_84(&zeta_i, re);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_84(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_84(re);
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
static KRML_MUSTINLINE Eurydice_arr_36
compute_vector_u_89(Eurydice_arr_e20 *a_as_ntt, Eurydice_arr_36 *r_as_ntt,
                    Eurydice_arr_36 *error_1) {
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_89(&lvalue););
  Eurydice_arr_36 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)2U, a_as_ntt, Eurydice_arr_36),
                Eurydice_arr_36);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_36 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_51),
                 Eurydice_arr_51);
         i++) {
      size_t j = i;
      Eurydice_arr_51 *a_element = &row->data[j];
      Eurydice_arr_51 product =
          ntt_multiply_d6_84(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_89(&result.data[i1], &product);
    }
    invert_ntt_montgomery_89(&result.data[i1]);
    add_error_reduce_d6_84(&result.data[i1], &error_1->data[i1]);
  }
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
static KRML_MUSTINLINE void compress_then_serialize_u_2d(Eurydice_arr_36 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, &input, Eurydice_arr_51),
               Eurydice_arr_51);
       i++) {
    size_t i0 = i;
    Eurydice_arr_51 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_a4(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_71 encrypt_c1_48(Eurydice_slice randomness,
                                              Eurydice_arr_e20 *matrix,
                                              Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_36 arr_struct0;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_48(&lvalue););
  Eurydice_arr_36 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_b4(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_48(&lvalue););
  Eurydice_arr_36 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_b4(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_41_490(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_51 error_2 = sample_from_binomial_distribution_89(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_36 u = compute_vector_u_89(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_2d(u, ciphertext);
  return (KRML_CLITERAL(tuple_71){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_51
compute_ring_element_v_89(Eurydice_arr_36 *t_as_ntt, Eurydice_arr_36 *r_as_ntt,
                          Eurydice_arr_51 *error_2, Eurydice_arr_51 *message) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_89(&result, &product););
  invert_ntt_montgomery_89(&result);
  return add_message_error_reduce_d6_84(error_2, message, result);
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
    Eurydice_arr_51 re, Eurydice_slice out) {
  compress_then_serialize_4_84(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_ba(Eurydice_arr_36 *t_as_ntt,
                                          Eurydice_arr_36 *r_as_ntt,
                                          Eurydice_arr_51 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_51 message_as_ring_element =
      deserialize_then_decompress_message_84(message);
  Eurydice_arr_51 v = compute_ring_element_v_89(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_unpacked_74(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_56 ciphertext = {.data = {0U}};
  tuple_71 uu____0 =
      encrypt_c1_48(randomness, &public_key->A,
                    Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                (size_t)640U, uint8_t *));
  Eurydice_arr_36 r_as_ntt = uu____0.fst;
  Eurydice_arr_51 error_2 = uu____0.snd;
  Eurydice_arr_36 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_36 *uu____2 = &r_as_ntt;
  Eurydice_arr_51 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_ba(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)768U, &ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
tuple_17 libcrux_ml_kem_ind_cca_unpacked_encapsulate_70(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_94 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_f8(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_56 ciphertext = encrypt_unpacked_74(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_17){
      .fst = libcrux_ml_kem_types_from_e0_d0(ciphertext),
      .snd = shared_secret_array});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static Eurydice_arr_51 call_mut_35_ba(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_36
deserialize_then_decompress_u_ba(Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_ba(&lvalue););
  Eurydice_arr_36 u_as_ntt = arr_struct;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)768U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_ee(u_bytes);
    ntt_vector_u_ee(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_51
deserialize_then_decompress_ring_element_v_29(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_84(serialized);
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
static KRML_MUSTINLINE Eurydice_arr_51
compute_message_89(Eurydice_arr_51 *v, Eurydice_arr_36 *secret_as_ntt,
                   Eurydice_arr_36 *u_as_ntt) {
  Eurydice_arr_51 result = ZERO_d6_84();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_51 product = ntt_multiply_d6_84(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_89(&result, &product););
  invert_ntt_montgomery_89(&result);
  return subtract_reduce_d6_84(v, result);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_4b(Eurydice_arr_36 *secret_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_36 u_as_ntt = deserialize_then_decompress_u_ba(ciphertext);
  Eurydice_arr_51 v = deserialize_then_decompress_ring_element_v_29(
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_51 message = compute_message_89(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_84(message);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_41
with const generics
- K= 2
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_41_49(Eurydice_slice input) {
  return PRF_9e(input);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_12(
    libcrux_ml_kem_mlkem512_avx2_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_4b(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_30 to_hash =
      libcrux_ml_kem_utils_into_padded_array_4d(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_41_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext = encrypt_unpacked_74(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
          Eurydice_array_to_slice((size_t)768U, &expected_ciphertext, uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 2
*/
static Eurydice_arr_51 call_mut_0b_89(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_36
deserialize_ring_elements_reduced_out_89(Eurydice_slice public_key) {
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_89(&lvalue););
  Eurydice_arr_36 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_89(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_29(
    Eurydice_arr_30 *public_key) {
  Eurydice_arr_36 deserialized_pk =
      deserialize_ring_elements_reduced_out_89(Eurydice_array_to_subslice_to(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_36 *uu____0 = &deserialized_pk;
  Eurydice_arr_30 public_key_serialized = serialize_public_key_29(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)800U, public_key, &public_key_serialized,
                           uint8_t);
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
    Eurydice_arr_7f *private_key) {
  Eurydice_arr_60 t = H_41_fd(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)2U,
      (size_t)768U * (size_t)2U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)2U + (size_t)32U,
      (size_t)768U * (size_t)2U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_7f *private_key, Eurydice_arr_56 *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_4d(private_key);
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
  Eurydice_arr_36 private_key = default_70_89();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94 public_key =
      default_8b_89();
  generate_keypair_unpacked_22(key_generation_seed, &private_key, &public_key);
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_7f *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_7f *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_7f *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_fd(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_7f *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE Eurydice_arr_7f serialize_kem_secret_key_4d(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_7f out = {.data = {0U}};
  serialize_kem_secret_key_mut_4d(private_key, public_key,
                                  implicit_rejection_value, &out);
  return out;
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
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_5d(ind_cpa_keypair_randomness);
  Eurydice_arr_56 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_30 public_key = uu____0.snd;
  Eurydice_arr_7f secret_key_serialized = serialize_kem_secret_key_4d(
      Eurydice_array_to_slice((size_t)768U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_7f private_key =
      libcrux_ml_kem_types_from_77_2a(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_fa(
      private_key, libcrux_ml_kem_types_from_fd_4d(public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_f8(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_89(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_e20 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_48 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_6c(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94
    build_unpacked_public_key_fa(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94
      unpacked_public_key = default_8b_89();
  build_unpacked_public_key_mut_fa(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_74(Eurydice_slice public_key,
                                                  Eurydice_arr_60 *message,
                                                  Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_94
      unpacked_public_key = build_unpacked_public_key_fa(public_key);
  return encrypt_unpacked_74(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_4d(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_17 libcrux_ml_kem_ind_cca_encapsulate_70(Eurydice_arr_30 *public_key,
                                               Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_f8(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_41_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_56 ciphertext =
      encrypt_74(Eurydice_array_to_slice(
                     (size_t)800U,
                     libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t),
                 &randomness0, pseudorandomness);
  Eurydice_arr_56 uu____2 = libcrux_ml_kem_types_from_e0_d0(ciphertext);
  return (
      KRML_CLITERAL(tuple_17){.fst = uu____2, .snd = kdf_39_4d(shared_secret)});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static Eurydice_arr_51 call_mut_0b_4b(void **_) { return ZERO_d6_84(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_4b(Eurydice_slice secret_key,
                                                  Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_36 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_4b(&lvalue););
  Eurydice_arr_36 secret_key_unpacked = arr_struct;
  deserialize_vector_89(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_4b(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_a1(
    Eurydice_arr_7f *private_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_4b(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_41_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_30 to_hash =
      libcrux_ml_kem_utils_into_padded_array_4d(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_41_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext =
      encrypt_74(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_4d(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_4d(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
}
