/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a8f2211d1b95e0462a96382023b164a4116c7ca4
 * Eurydice: 60f543ddc60a777138070968daaf7620ec48170d
 * Karamel: 1d81d757d5d9e16dd6463ccc72324e587c707959
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: 072dd6530cbd58bb23ba8e0fabab8141aa9de3b7
 */

#ifndef __libcrux_mldsa65_avx2_H
#define __libcrux_mldsa65_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_core.h"
#include "libcrux_mldsa65_portable.h"
#include "libcrux_sha3_avx2.h"
#include "libcrux_sha3_portable.h"

typedef libcrux_sha3_avx2_x4_incremental_KeccakState
    libcrux_ml_dsa_hash_functions_simd256_Shake128x4;

/**
 Init the state and absorb 4 blocks in parallel.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb(Eurydice_slice input0,
                                                  Eurydice_slice input1,
                                                  Eurydice_slice input2,
                                                  Eurydice_slice input3) {
  libcrux_sha3_generic_keccak_KeccakState_55 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(&state, input0, input1,
                                                         input2, input3);
  return state;
}

typedef libcrux_sha3_portable_KeccakState
    libcrux_ml_dsa_hash_functions_simd256_Shake256;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_portable_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb_final_shake256(
    Eurydice_slice input) {
  libcrux_sha3_generic_keccak_KeccakState_17 state =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state, input);
  return state;
}

typedef libcrux_sha3_avx2_x4_incremental_KeccakState
    libcrux_ml_dsa_hash_functions_simd256_Shake256x4;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb_x4(Eurydice_slice input0,
                                                     Eurydice_slice input1,
                                                     Eurydice_slice input2,
                                                     Eurydice_slice input3) {
  libcrux_sha3_generic_keccak_KeccakState_55 state =
      libcrux_sha3_avx2_x4_incremental_init();
  libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(&state, input0, input1,
                                                         input2, input3);
  return state;
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_shake256(
    libcrux_sha3_portable_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_x4(
    libcrux_sha3_avx2_x4_incremental_KeccakState *state) {
  uint8_t out0[136U] = {0U};
  uint8_t out1[136U] = {0U};
  uint8_t out2[136U] = {0U};
  uint8_t out3[136U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice((size_t)136U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_five_blocks(
    libcrux_sha3_avx2_x4_incremental_KeccakState *state, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
      state, Eurydice_array_to_slice((size_t)840U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)840U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)840U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)840U, out3, uint8_t));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_168size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *state) {
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      state, Eurydice_array_to_slice((size_t)168U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[168U];
  memcpy(copy_of_out0, out0, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[168U];
  memcpy(copy_of_out1, out1, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[168U];
  memcpy(copy_of_out2, out2, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[168U];
  memcpy(copy_of_out3, out3, (size_t)168U * sizeof(uint8_t));
  uint8_t_168size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)168U * sizeof(uint8_t));
  return lit;
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_shake256(
    libcrux_sha3_portable_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4(
    libcrux_sha3_avx2_x4_incremental_KeccakState *state) {
  uint8_t out0[136U] = {0U};
  uint8_t out1[136U] = {0U};
  uint8_t out2[136U] = {0U};
  uint8_t out3[136U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice((size_t)136U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

/**
 Init the state and absorb 4 blocks in parallel.
*/
/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake128x4)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb_7b(Eurydice_slice input0,
                                                     Eurydice_slice input1,
                                                     Eurydice_slice input2,
                                                     Eurydice_slice input3) {
  return libcrux_ml_dsa_hash_functions_simd256_init_absorb(input0, input1,
                                                           input2, input3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake128x4)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_five_blocks_7b(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_ml_dsa_hash_functions_simd256_squeeze_first_five_blocks(
      self, out0, out1, out2, out3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake128x4)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_168size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_7b(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self) {
  return libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block(self);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_portable_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb_final_d9(
    Eurydice_slice input) {
  return libcrux_ml_dsa_hash_functions_simd256_init_absorb_final_shake256(
      input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_d9(
    libcrux_sha3_portable_KeccakState *self, uint8_t ret[136U]) {
  libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_shake256(self, ret);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_d9(
    libcrux_sha3_portable_KeccakState *self, uint8_t ret[136U]) {
  libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_shake256(self, ret);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake256x4)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_ml_dsa_hash_functions_simd256_init_absorb_x4_fb(Eurydice_slice input0,
                                                        Eurydice_slice input1,
                                                        Eurydice_slice input2,
                                                        Eurydice_slice input3) {
  return libcrux_ml_dsa_hash_functions_simd256_init_absorb_x4(input0, input1,
                                                              input2, input3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake256x4)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_x4_fb(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self) {
  return libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_x4(self);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake256x4)#2}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4_fb(
    libcrux_sha3_avx2_x4_incremental_KeccakState *self) {
  return libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4(self);
}

typedef __m256i libcrux_ml_dsa_simd_avx2_vector_type_Vec256;

/**
 Create an all-zero vector coefficient
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_dsa_simd_avx2_vector_type_zero(void) {
  return libcrux_intrinsics_avx2_mm256_setzero_si256();
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_dsa_simd_avx2_zero_22(void) {
  return libcrux_ml_dsa_simd_avx2_vector_type_zero();
}

/**
 Create a coefficient from an `i32` array
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_vector_type_from_coefficient_array(
    Eurydice_slice coefficient_array, __m256i *out) {
  out[0U] = libcrux_intrinsics_avx2_mm256_loadu_si256_i32(coefficient_array);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_from_coefficient_array_22(
    Eurydice_slice coefficient_array, __m256i *out) {
  libcrux_ml_dsa_simd_avx2_vector_type_from_coefficient_array(coefficient_array,
                                                              out);
}

/**
 Write out the coefficient to an `i32` array
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_vector_type_to_coefficient_array(__m256i *value,
                                                          Eurydice_slice out) {
  libcrux_intrinsics_avx2_mm256_storeu_si256_i32(out, value[0U]);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_to_coefficient_array_22(
    __m256i *value, Eurydice_slice out) {
  libcrux_ml_dsa_simd_avx2_vector_type_to_coefficient_array(value, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_arithmetic_add(
    __m256i *lhs, __m256i *rhs) {
  lhs[0U] = libcrux_intrinsics_avx2_mm256_add_epi32(lhs[0U], rhs[0U]);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_add_22(__m256i *lhs,
                                                            __m256i *rhs) {
  libcrux_ml_dsa_simd_avx2_arithmetic_add(lhs, rhs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_arithmetic_subtract(
    __m256i *lhs, __m256i *rhs) {
  lhs[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(lhs[0U], rhs[0U]);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_subtract_22(__m256i *lhs,
                                                                 __m256i *rhs) {
  libcrux_ml_dsa_simd_avx2_arithmetic_subtract(lhs, rhs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_simd_avx2_arithmetic_infinity_norm_exceeds(__m256i *simd_unit,
                                                          int32_t bound) {
  __m256i absolute_values =
      libcrux_intrinsics_avx2_mm256_abs_epi32(simd_unit[0U]);
  __m256i bound0 = libcrux_intrinsics_avx2_mm256_set1_epi32(bound - (int32_t)1);
  __m256i compare_with_bound =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi32(absolute_values, bound0);
  int32_t result = libcrux_intrinsics_avx2_mm256_testz_si256(
      compare_with_bound, compare_with_bound);
  return result != (int32_t)1;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_dsa_simd_avx2_infinity_norm_exceeds_22(
    __m256i *simd_unit, int32_t bound) {
  return libcrux_ml_dsa_simd_avx2_arithmetic_infinity_norm_exceeds(simd_unit,
                                                                   bound);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_arithmetic_to_unsigned_representatives_ret(
    __m256i *t) {
  __m256i signs =
      libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)31, t[0U], __m256i);
  __m256i conditional_add_field_modulus =
      libcrux_intrinsics_avx2_mm256_and_si256(
          signs, libcrux_intrinsics_avx2_mm256_set1_epi32(
                     LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS));
  return libcrux_intrinsics_avx2_mm256_add_epi32(t[0U],
                                                 conditional_add_field_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_arithmetic_decompose(
    int32_t gamma2, __m256i *r, __m256i *r0, __m256i *r1) {
  __m256i r2 =
      libcrux_ml_dsa_simd_avx2_arithmetic_to_unsigned_representatives_ret(r);
  __m256i ceil_of_r_by_128 = libcrux_intrinsics_avx2_mm256_add_epi32(
      r2, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)127));
  __m256i ceil_of_r_by_1280 = libcrux_intrinsics_avx2_mm256_srai_epi32(
      (int32_t)7, ceil_of_r_by_128, __m256i);
  switch (gamma2) {
    case 95232: {
      __m256i result = libcrux_intrinsics_avx2_mm256_mullo_epi32(
          ceil_of_r_by_1280,
          libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)11275));
      __m256i result0 = libcrux_intrinsics_avx2_mm256_add_epi32(
          result, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1 << 23U));
      __m256i result1 = libcrux_intrinsics_avx2_mm256_srai_epi32(
          (int32_t)24, result0, __m256i);
      __m256i mask = libcrux_intrinsics_avx2_mm256_sub_epi32(
          libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)43), result1);
      __m256i mask0 =
          libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)31, mask, __m256i);
      __m256i not_result =
          libcrux_intrinsics_avx2_mm256_xor_si256(result1, mask0);
      r1[0U] = libcrux_intrinsics_avx2_mm256_and_si256(result1, not_result);
      break;
    }
    case 261888: {
      __m256i result = libcrux_intrinsics_avx2_mm256_mullo_epi32(
          ceil_of_r_by_1280,
          libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1025));
      __m256i result0 = libcrux_intrinsics_avx2_mm256_add_epi32(
          result, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1 << 21U));
      __m256i result1 = libcrux_intrinsics_avx2_mm256_srai_epi32(
          (int32_t)22, result0, __m256i);
      r1[0U] = libcrux_intrinsics_avx2_mm256_and_si256(
          result1, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)15));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  int32_t alpha = gamma2 * (int32_t)2;
  __m256i r0_tmp = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      r1[0U], libcrux_intrinsics_avx2_mm256_set1_epi32(alpha));
  __m256i r0_tmp0 = libcrux_intrinsics_avx2_mm256_sub_epi32(r2, r0_tmp);
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS - (int32_t)1) / (int32_t)2);
  __m256i mask =
      libcrux_intrinsics_avx2_mm256_sub_epi32(field_modulus_halved, r0_tmp0);
  __m256i mask0 =
      libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)31, mask, __m256i);
  __m256i field_modulus_and_mask = libcrux_intrinsics_avx2_mm256_and_si256(
      mask0, libcrux_intrinsics_avx2_mm256_set1_epi32(
                 LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS));
  r0[0U] =
      libcrux_intrinsics_avx2_mm256_sub_epi32(r0_tmp0, field_modulus_and_mask);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_decompose_22(
    int32_t gamma2, __m256i *simd_unit, __m256i *low, __m256i *high) {
  libcrux_ml_dsa_simd_avx2_arithmetic_decompose(gamma2, simd_unit, low, high);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t libcrux_ml_dsa_simd_avx2_arithmetic_compute_hint(
    __m256i *low, __m256i *high, int32_t gamma2, __m256i *hint) {
  __m256i minus_gamma2 = libcrux_intrinsics_avx2_mm256_set1_epi32(-gamma2);
  __m256i gamma20 = libcrux_intrinsics_avx2_mm256_set1_epi32(gamma2);
  __m256i low_within_bound = libcrux_intrinsics_avx2_mm256_cmpgt_epi32(
      libcrux_intrinsics_avx2_mm256_abs_epi32(low[0U]), gamma20);
  __m256i low_equals_minus_gamma2 =
      libcrux_intrinsics_avx2_mm256_cmpeq_epi32(low[0U], minus_gamma2);
  __m256i low_equals_minus_gamma2_and_high_is_nonzero =
      libcrux_intrinsics_avx2_mm256_sign_epi32(low_equals_minus_gamma2,
                                               high[0U]);
  hint[0U] = libcrux_intrinsics_avx2_mm256_or_si256(
      low_within_bound, low_equals_minus_gamma2_and_high_is_nonzero);
  int32_t hints_mask = libcrux_intrinsics_avx2_mm256_movemask_ps(
      libcrux_intrinsics_avx2_mm256_castsi256_ps(hint[0U]));
  hint[0U] = libcrux_intrinsics_avx2_mm256_and_si256(
      hint[0U], libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1));
  return (size_t)core_num__i32_2__count_ones(hints_mask);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t libcrux_ml_dsa_simd_avx2_compute_hint_22(
    __m256i *low, __m256i *high, int32_t gamma2, __m256i *hint) {
  return libcrux_ml_dsa_simd_avx2_arithmetic_compute_hint(low, high, gamma2,
                                                          hint);
}

typedef struct core_core_arch_x86___m256i_x2_s {
  __m256i fst;
  __m256i snd;
} core_core_arch_x86___m256i_x2;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_arithmetic_use_hint(
    int32_t gamma2, __m256i *r, __m256i *hint) {
  core_core_arch_x86___m256i_x2 uu____0 = {
      .fst = libcrux_intrinsics_avx2_mm256_setzero_si256(),
      .snd = libcrux_intrinsics_avx2_mm256_setzero_si256()};
  __m256i r0 = uu____0.fst;
  __m256i r1 = uu____0.snd;
  libcrux_ml_dsa_simd_avx2_arithmetic_decompose(gamma2, r, &r0, &r1);
  __m256i all_zeros = libcrux_intrinsics_avx2_mm256_setzero_si256();
  __m256i negate_hints =
      libcrux_intrinsics_avx2_vec256_blendv_epi32(all_zeros, hint[0U], r0);
  __m256i negate_hints0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, negate_hints, __m256i);
  __m256i hints =
      libcrux_intrinsics_avx2_mm256_sub_epi32(hint[0U], negate_hints0);
  __m256i r1_plus_hints = libcrux_intrinsics_avx2_mm256_add_epi32(r1, hints);
  switch (gamma2) {
    case 95232: {
      __m256i max = libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)43);
      r1_plus_hints = libcrux_intrinsics_avx2_vec256_blendv_epi32(
          r1_plus_hints, max, r1_plus_hints);
      __m256i greater_than_or_equal_to_max =
          libcrux_intrinsics_avx2_mm256_cmpgt_epi32(r1_plus_hints, max);
      hint[0U] = libcrux_intrinsics_avx2_vec256_blendv_epi32(
          r1_plus_hints, all_zeros, greater_than_or_equal_to_max);
      break;
    }
    case 261888: {
      hint[0U] = libcrux_intrinsics_avx2_mm256_and_si256(
          r1_plus_hints, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)15));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_use_hint_22(
    int32_t gamma2, __m256i *simd_unit, __m256i *hint) {
  libcrux_ml_dsa_simd_avx2_arithmetic_use_hint(gamma2, simd_unit, hint);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(__m256i *lhs,
                                                        __m256i *rhs) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  __m256i inverse_of_modulus_mod_montgomery_r =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R);
  __m256i prod02 = libcrux_intrinsics_avx2_mm256_mul_epi32(lhs[0U], rhs[0U]);
  __m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, lhs[0U],
                                                  __m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, rhs[0U],
                                                  __m256i));
  __m256i k02 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod02, inverse_of_modulus_mod_montgomery_r);
  __m256i k13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod13, inverse_of_modulus_mod_montgomery_r);
  __m256i c02 = libcrux_intrinsics_avx2_mm256_mul_epi32(k02, field_modulus);
  __m256i c13 = libcrux_intrinsics_avx2_mm256_mul_epi32(k13, field_modulus);
  __m256i res02 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod02, c02);
  __m256i res13 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod13, c13);
  __m256i res02_shifted =
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, res02, __m256i);
  lhs[0U] = libcrux_intrinsics_avx2_mm256_blend_epi32(
      (int32_t)170, res02_shifted, res13, __m256i);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_montgomery_multiply_22(
    __m256i *lhs, __m256i *rhs) {
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(lhs, rhs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_arithmetic_to_unsigned_representatives(__m256i *t) {
  t[0U] =
      libcrux_ml_dsa_simd_avx2_arithmetic_to_unsigned_representatives_ret(t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_arithmetic_power2round(
    __m256i *r0, __m256i *r1) {
  libcrux_ml_dsa_simd_avx2_arithmetic_to_unsigned_representatives(r0);
  r1[0U] = libcrux_intrinsics_avx2_mm256_add_epi32(
      r0[0U],
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          ((int32_t)1
           << (uint32_t)(LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                         (size_t)1U)) -
          (int32_t)1));
  r1[0U] =
      libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)13, r1[0U], __m256i);
  __m256i tmp =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)13, r1[0U], __m256i);
  r0[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(r0[0U], tmp);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_power2round_22(
    __m256i *t0, __m256i *t1) {
  libcrux_ml_dsa_simd_avx2_arithmetic_power2round(t0, t1);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_REJECTION_SAMPLE_LESS_THAN_FIELD_MODULUS_BYTESTREAM_TO_POTENTIAL_COEFFICIENTS_COEFFICIENT_MASK \
  (((int32_t)1 << 23U) - (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_bytestream_to_potential_coefficients(
    Eurydice_slice serialized) {
  uint8_t serialized_extended[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_to((size_t)32U, serialized_extended,
                                    (size_t)24U, uint8_t, size_t),
      serialized, uint8_t);
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, serialized_extended, uint8_t));
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi32(
                        (int32_t)0, (int32_t)5, (int32_t)4, (int32_t)3,
                        (int32_t)0, (int32_t)2, (int32_t)1, (int32_t)0));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      coefficients0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)-1, (int8_t)8,
          (int8_t)7, (int8_t)6, (int8_t)-1, (int8_t)5, (int8_t)4, (int8_t)3,
          (int8_t)-1, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1, (int8_t)11,
          (int8_t)10, (int8_t)9, (int8_t)-1, (int8_t)8, (int8_t)7, (int8_t)6,
          (int8_t)-1, (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)-1, (int8_t)2,
          (int8_t)1, (int8_t)0));
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients1,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_REJECTION_SAMPLE_LESS_THAN_FIELD_MODULUS_BYTESTREAM_TO_POTENTIAL_COEFFICIENTS_COEFFICIENT_MASK));
}

static const uint8_t
    libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE
        [16U][16U] = {{255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U},
                      {4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U},
                      {8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U},
                      {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U,
                       255U, 255U, 255U},
                      {12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U},
                      {4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U, 255U,
                       255U, 255U, 255U},
                      {8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                       255U, 255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                       255U, 255U, 255U, 255U},
                      {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                       255U, 255U, 255U, 255U},
                      {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U,
                       13U, 14U, 15U}};

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_sample(
    Eurydice_slice input, Eurydice_slice output) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  __m256i potential_coefficients =
      libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_bytestream_to_potential_coefficients(
          input);
  __m256i compare_with_field_modulus =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi32(field_modulus,
                                                potential_coefficients);
  int32_t good = libcrux_intrinsics_avx2_mm256_movemask_ps(
      libcrux_intrinsics_avx2_mm256_castsi256_ps(compare_with_field_modulus));
  int32_t good_lower_half = good & (int32_t)15;
  int32_t good_upper_half = good >> 4U;
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_lower_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(potential_coefficients);
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, (size_t)0U, (size_t)4U, int32_t),
      lower_coefficients0);
  size_t sampled_count = (size_t)core_num__i32_2__count_ones(good_lower_half);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_upper_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, potential_coefficients, __m128i);
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)4U, int32_t),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__i32_2__count_ones(good_upper_half);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_22(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_sample(
      randomness, out);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_DESERIALIZE_TO_UNSIGNED_WHEN_ETA_IS_4_COEFFICIENT_MASK \
  (((int32_t)1 << 4U) - (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned_when_eta_is_4(
    Eurydice_slice bytes) {
  __m256i bytes_in_simd_unit = libcrux_intrinsics_avx2_mm256_set_epi32(
      (int32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      bytes_in_simd_unit, libcrux_intrinsics_avx2_mm256_set_epi32(
                              (int32_t)4, (int32_t)0, (int32_t)4, (int32_t)0,
                              (int32_t)4, (int32_t)0, (int32_t)4, (int32_t)0));
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_DESERIALIZE_TO_UNSIGNED_WHEN_ETA_IS_4_COEFFICIENT_MASK));
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_DESERIALIZE_TO_UNSIGNED_WHEN_ETA_IS_2_COEFFICIENT_MASK \
  (((int32_t)1 << 3U) - (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned_when_eta_is_2(
    Eurydice_slice bytes) {
  __m256i bytes_in_simd_unit = libcrux_intrinsics_avx2_mm256_set_epi32(
      (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)
              << 8U |
          (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)
              << 8U |
          (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
      (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      bytes_in_simd_unit, libcrux_intrinsics_avx2_mm256_set_epi32(
                              (int32_t)5, (int32_t)2, (int32_t)7, (int32_t)4,
                              (int32_t)1, (int32_t)6, (int32_t)3, (int32_t)0));
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_DESERIALIZE_TO_UNSIGNED_WHEN_ETA_IS_2_COEFFICIENT_MASK));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice serialized) {
  if (!(eta == libcrux_ml_dsa_constants_Eta_Two)) {
    return libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned_when_eta_is_4(
        serialized);
  }
  return libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned_when_eta_is_2(
      serialized);
}

/**
A monomorphic instance of
libcrux_ml_dsa.simd.avx2.rejection_sample.less_than_eta.shift_interval with
const generics
- ETA= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_shift_interval_fd(
    __m256i coefficients) {
  __m256i uu____0;
  __m256i quotient = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)26));
  __m256i quotient0 =
      libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)7, quotient, __m256i);
  __m256i quotient1 = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      quotient0, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)5));
  __m256i coefficients_mod_5 =
      libcrux_intrinsics_avx2_mm256_sub_epi32(coefficients, quotient1);
  uu____0 = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)(size_t)2U),
      coefficients_mod_5);
  return uu____0;
}

/**
A monomorphic instance of
libcrux_ml_dsa.simd.avx2.rejection_sample.less_than_eta.sample with const
generics
- ETA= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_sample_fd(
    Eurydice_slice input, Eurydice_slice output) {
  __m256i potential_coefficients =
      libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned(
          libcrux_ml_dsa_constants_Eta_Four, input);
  int32_t interval_boundary;
  interval_boundary = (int32_t)15;
  __m256i compare_with_interval_boundary =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi32(
          libcrux_intrinsics_avx2_mm256_set1_epi32(interval_boundary),
          potential_coefficients);
  int32_t good = libcrux_intrinsics_avx2_mm256_movemask_ps(
      libcrux_intrinsics_avx2_mm256_castsi256_ps(
          compare_with_interval_boundary));
  int32_t good_lower_half = good & (int32_t)15;
  int32_t good_upper_half = good >> 4U;
  __m256i shifted =
      libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_shift_interval_fd(
          potential_coefficients);
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_lower_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(shifted);
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, (size_t)0U, (size_t)4U, int32_t),
      lower_coefficients0);
  size_t sampled_count = (size_t)core_num__i32_2__count_ones(good_lower_half);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_upper_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, shifted, __m128i);
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)4U, int32_t),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__i32_2__count_ones(good_upper_half);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_equals_2_22(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_sample_fd(
      randomness, out);
}

/**
A monomorphic instance of
libcrux_ml_dsa.simd.avx2.rejection_sample.less_than_eta.shift_interval with
const generics
- ETA= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_shift_interval_ac(
    __m256i coefficients) {
  return libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)(size_t)4U),
      coefficients);
}

/**
A monomorphic instance of
libcrux_ml_dsa.simd.avx2.rejection_sample.less_than_eta.sample with const
generics
- ETA= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_sample_ac(
    Eurydice_slice input, Eurydice_slice output) {
  __m256i potential_coefficients =
      libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned(
          libcrux_ml_dsa_constants_Eta_Four, input);
  int32_t interval_boundary;
  interval_boundary = (int32_t)9;
  __m256i compare_with_interval_boundary =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi32(
          libcrux_intrinsics_avx2_mm256_set1_epi32(interval_boundary),
          potential_coefficients);
  int32_t good = libcrux_intrinsics_avx2_mm256_movemask_ps(
      libcrux_intrinsics_avx2_mm256_castsi256_ps(
          compare_with_interval_boundary));
  int32_t good_lower_half = good & (int32_t)15;
  int32_t good_upper_half = good >> 4U;
  __m256i shifted =
      libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_shift_interval_ac(
          potential_coefficients);
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_lower_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(shifted);
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, (size_t)0U, (size_t)4U, int32_t),
      lower_coefficients0);
  size_t sampled_count = (size_t)core_num__i32_2__count_ones(good_lower_half);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_SHUFFLE_TABLE[(
             size_t)good_upper_half],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, shifted, __m128i);
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128_i32(
      Eurydice_slice_subslice2(output, sampled_count,
                               sampled_count + (size_t)4U, int32_t),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__i32_2__count_ones(good_upper_half);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_equals_4_22(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_sample_ac(
      randomness, out);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[32U] = {0U};
  __m256i simd_unit_shifted = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1),
      simd_unit[0U]);
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit_shifted, libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)14, (int32_t)0, (int32_t)14,
                             (int32_t)0, (int32_t)14, (int32_t)0, (int32_t)14));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)14, adjacent_2_combined, __m256i);
  __m256i every_second_element = libcrux_intrinsics_avx2_mm256_bsrli_epi128(
      (int32_t)8, adjacent_2_combined0, __m256i);
  __m256i every_second_element_shifted =
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)36,
                                               every_second_element, __m256i);
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_add_epi64(
      adjacent_2_combined0, every_second_element_shifted);
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srlv_epi64(
      adjacent_4_combined,
      libcrux_intrinsics_avx2_mm256_set_epi64x((int64_t)28, (int64_t)0,
                                               (int64_t)28, (int64_t)0));
  __m128i lower_4 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_4_combined0);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_4);
  __m128i upper_4 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_4_combined0, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)9U, (size_t)25U, uint8_t),
      upper_4);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)18U, uint8_t),
      uint8_t);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[32U] = {0U};
  __m256i simd_unit_shifted = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1),
      simd_unit[0U]);
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit_shifted, libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12,
                             (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)12, adjacent_2_combined, __m256i);
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_2_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
          (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)4,
          (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  __m128i lower_4 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_4_combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_4);
  __m128i upper_4 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_4_combined, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)10U, (size_t)26U,
                                  uint8_t),
      upper_4);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)20U, uint8_t),
      uint8_t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize(
    __m256i *simd_unit, Eurydice_slice serialized, size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
          simd_unit, serialized);
      break;
    }
    case 19U: {
      libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
          simd_unit, serialized);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_gamma1_serialize_22(
    __m256i *simd_unit, Eurydice_slice serialized, size_t gamma1_exponent) {
  libcrux_ml_dsa_simd_avx2_encoding_gamma1_serialize(simd_unit, serialized,
                                                     gamma1_exponent);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_MASK \
  ((LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1                  \
    << 1U) -                                                                                             \
   (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_slice serialized, __m256i *out) {
  __m128i serialized_lower = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t));
  __m128i serialized_upper = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(serialized, (size_t)2U, (size_t)18U, uint8_t));
  __m256i serialized0 = libcrux_intrinsics_avx2_mm256_set_m128i(
      serialized_upper, serialized_lower);
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      serialized0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)15, (int8_t)14, (int8_t)13, (int8_t)-1,
          (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)-1, (int8_t)11,
          (int8_t)10, (int8_t)9, (int8_t)-1, (int8_t)9, (int8_t)8, (int8_t)7,
          (int8_t)-1, (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)-1, (int8_t)6,
          (int8_t)5, (int8_t)4, (int8_t)-1, (int8_t)4, (int8_t)3, (int8_t)2,
          (int8_t)-1, (int8_t)2, (int8_t)1, (int8_t)0));
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi32(
                        (int32_t)6, (int32_t)4, (int32_t)2, (int32_t)0,
                        (int32_t)6, (int32_t)4, (int32_t)2, (int32_t)0));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients0,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_MASK));
  out[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1),
      coefficients1);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_MASK \
  ((LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1                  \
    << 1U) -                                                                                             \
   (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_slice serialized, __m256i *out) {
  __m128i serialized_lower = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t));
  __m128i serialized_upper = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice2(serialized, (size_t)4U, (size_t)20U, uint8_t));
  __m256i serialized0 = libcrux_intrinsics_avx2_mm256_set_m128i(
      serialized_upper, serialized_lower);
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      serialized0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)15, (int8_t)14, (int8_t)13, (int8_t)-1,
          (int8_t)13, (int8_t)12, (int8_t)11, (int8_t)-1, (int8_t)10, (int8_t)9,
          (int8_t)8, (int8_t)-1, (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)-1,
          (int8_t)9, (int8_t)8, (int8_t)7, (int8_t)-1, (int8_t)7, (int8_t)6,
          (int8_t)5, (int8_t)-1, (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)-1,
          (int8_t)2, (int8_t)1, (int8_t)0));
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi32(
                        (int32_t)4, (int32_t)0, (int32_t)4, (int32_t)0,
                        (int32_t)4, (int32_t)0, (int32_t)4, (int32_t)0));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients0,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_MASK));
  out[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1),
      coefficients1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize(Eurydice_slice serialized,
                                                     __m256i *out,
                                                     size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
          serialized, out);
      break;
    }
    case 19U: {
      libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
          serialized, out);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_gamma1_deserialize_22(
    Eurydice_slice serialized, __m256i *out, size_t gamma1_exponent) {
  libcrux_ml_dsa_simd_avx2_encoding_gamma1_deserialize(serialized, out,
                                                       gamma1_exponent);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_commitment_serialize(__m256i *simd_unit,
                                                       Eurydice_slice out) {
  uint8_t serialized[19U] = {0U};
  switch ((uint8_t)Eurydice_slice_len(out, uint8_t)) {
    case 4U: {
      __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
          simd_unit[0U], libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)28, (int32_t)0, (int32_t)28,
                             (int32_t)0, (int32_t)28, (int32_t)0, (int32_t)28));
      __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
          (int32_t)28, adjacent_2_combined, __m256i);
      __m256i adjacent_4_combined =
          libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
              adjacent_2_combined0,
              libcrux_intrinsics_avx2_mm256_set_epi32(
                  (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)6,
                  (int32_t)2, (int32_t)4, (int32_t)0));
      __m128i adjacent_4_combined0 =
          libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_4_combined);
      __m128i adjacent_4_combined1 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
          adjacent_4_combined0,
          libcrux_intrinsics_avx2_mm_set_epi8(240U, 240U, 240U, 240U, 240U,
                                              240U, 240U, 240U, 240U, 240U,
                                              240U, 240U, 12U, 4U, 8U, 0U));
      libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
          Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U,
                                      uint8_t),
          adjacent_4_combined1);
      Eurydice_slice uu____0 = out;
      Eurydice_slice_copy(uu____0,
                          Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                      (size_t)4U, uint8_t),
                          uint8_t);
      break;
    }
    case 6U: {
      __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
          simd_unit[0U], libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)26, (int32_t)0, (int32_t)26,
                             (int32_t)0, (int32_t)26, (int32_t)0, (int32_t)26));
      __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
          (int32_t)26, adjacent_2_combined, __m256i);
      __m256i adjacent_3_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
          adjacent_2_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi8(
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)9, (int8_t)8, (int8_t)1,
              (int8_t)0, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
              (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)9, (int8_t)8,
              (int8_t)1, (int8_t)0));
      __m256i adjacent_3_combined0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
          adjacent_3_combined,
          libcrux_intrinsics_avx2_mm256_set_epi16(
              (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1,
              (int16_t)1, (int16_t)1, (int16_t)1 << 4U, (int16_t)1, (int16_t)1,
              (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)1,
              (int16_t)1 << 4U));
      __m256i adjacent_3_combined1 = libcrux_intrinsics_avx2_mm256_srlv_epi32(
          adjacent_3_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)4, (int32_t)0,
              (int32_t)0, (int32_t)0, (int32_t)4));
      __m128i lower_3 =
          libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_3_combined1);
      libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
          Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U,
                                      uint8_t),
          lower_3);
      __m128i upper_3 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
          (int32_t)1, adjacent_3_combined1, __m128i);
      libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
          Eurydice_array_to_subslice2(serialized, (size_t)3U, (size_t)19U,
                                      uint8_t),
          upper_3);
      Eurydice_slice uu____1 = out;
      Eurydice_slice_copy(uu____1,
                          Eurydice_array_to_subslice2(serialized, (size_t)0U,
                                                      (size_t)6U, uint8_t),
                          uint8_t);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_commitment_serialize_22(
    __m256i *simd_unit, Eurydice_slice serialized) {
  libcrux_ml_dsa_simd_avx2_encoding_commitment_serialize(simd_unit, serialized);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_error_serialize_when_eta_is_4(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[16U] = {0U};
  __m256i simd_unit_shifted = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA),
      simd_unit[0U]);
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit_shifted, libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)28, (int32_t)0, (int32_t)28,
                             (int32_t)0, (int32_t)28, (int32_t)0, (int32_t)28));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)28, adjacent_2_combined, __m256i);
  __m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
          adjacent_2_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)6,
              (int32_t)2, (int32_t)4, (int32_t)0));
  __m128i adjacent_4_combined0 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_4_combined);
  __m128i adjacent_4_combined1 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      adjacent_4_combined0, libcrux_intrinsics_avx2_mm_set_epi8(
                                240U, 240U, 240U, 240U, 240U, 240U, 240U, 240U,
                                240U, 240U, 240U, 240U, 12U, 4U, 8U, 0U));
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      adjacent_4_combined1);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)4U, uint8_t),
      uint8_t);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_encoding_error_serialize_when_eta_is_2(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[16U] = {0U};
  __m256i simd_unit_shifted = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA),
      simd_unit[0U]);
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit_shifted, libcrux_intrinsics_avx2_mm256_set_epi32(
                             (int32_t)0, (int32_t)29, (int32_t)0, (int32_t)29,
                             (int32_t)0, (int32_t)29, (int32_t)0, (int32_t)29));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)29, adjacent_2_combined, __m256i);
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_2_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)8, (int8_t)-1, (int8_t)0,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)8, (int8_t)-1,
          (int8_t)0));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_madd_epi16(
      adjacent_4_combined,
      libcrux_intrinsics_avx2_mm256_set_epi16(
          (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
          (int16_t)0, (int16_t)1 << 6U, (int16_t)1, (int16_t)0, (int16_t)0,
          (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)1 << 6U,
          (int16_t)1));
  __m256i adjacent_6_combined =
      libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
          adjacent_4_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
              (int32_t)0, (int32_t)4, (int32_t)0));
  __m128i adjacent_6_combined0 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_6_combined);
  __m128i adjacent_6_combined1 = libcrux_intrinsics_avx2_mm_sllv_epi32(
      adjacent_6_combined0,
      libcrux_intrinsics_avx2_mm_set_epi32((int32_t)0, (int32_t)0, (int32_t)0,
                                           (int32_t)20));
  __m128i adjacent_6_combined2 = libcrux_intrinsics_avx2_mm_srli_epi64(
      (int32_t)20, adjacent_6_combined1, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      adjacent_6_combined2);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)3U, uint8_t),
      uint8_t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_error_serialize(
    libcrux_ml_dsa_constants_Eta eta, __m256i *simd_unit,
    Eurydice_slice serialized) {
  void *uu____0 = (void *)0U;
  if (!(eta == libcrux_ml_dsa_constants_Eta_Two)) {
    libcrux_ml_dsa_simd_avx2_encoding_error_serialize_when_eta_is_4(simd_unit,
                                                                    serialized);
    return;
  }
  libcrux_ml_dsa_simd_avx2_encoding_error_serialize_when_eta_is_2(simd_unit,
                                                                  serialized);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_error_serialize_22(
    libcrux_ml_dsa_constants_Eta eta, __m256i *simd_unit,
    Eurydice_slice serialized) {
  libcrux_ml_dsa_simd_avx2_encoding_error_serialize(eta, simd_unit, serialized);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_error_deserialize(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice serialized, __m256i *out) {
  __m256i unsigned0 =
      libcrux_ml_dsa_simd_avx2_encoding_error_deserialize_to_unsigned(
          eta, serialized);
  int32_t eta0;
  if (eta == libcrux_ml_dsa_constants_Eta_Two) {
    eta0 = (int32_t)2;
  } else {
    eta0 = (int32_t)4;
  }
  out[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(
      libcrux_intrinsics_avx2_mm256_set1_epi32(eta0), unsigned0);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_error_deserialize_22(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice serialized, __m256i *out) {
  libcrux_ml_dsa_simd_avx2_encoding_error_deserialize(eta, serialized, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_encoding_t0_change_interval(__m256i *simd_unit) {
  __m256i interval_end = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1
      << (uint32_t)(LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                    (size_t)1U));
  return libcrux_intrinsics_avx2_mm256_sub_epi32(interval_end, simd_unit[0U]);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_t0_serialize(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[16U] = {0U};
  __m256i simd_unit0 =
      libcrux_ml_dsa_simd_avx2_encoding_t0_change_interval(simd_unit);
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit0, libcrux_intrinsics_avx2_mm256_set_epi32(
                      (int32_t)0, (int32_t)19, (int32_t)0, (int32_t)19,
                      (int32_t)0, (int32_t)19, (int32_t)0, (int32_t)19));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)19, adjacent_2_combined, __m256i);
  __m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
          adjacent_2_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)6,
              (int32_t)4, (int32_t)2, (int32_t)0));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_4_combined, libcrux_intrinsics_avx2_mm256_set_epi32(
                               (int32_t)0, (int32_t)6, (int32_t)0, (int32_t)6,
                               (int32_t)0, (int32_t)6, (int32_t)0, (int32_t)6));
  __m256i adjacent_4_combined1 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)6, adjacent_4_combined0, __m256i);
  __m256i second_4_combined = libcrux_intrinsics_avx2_mm256_bsrli_epi128(
      (int32_t)8, adjacent_4_combined1, __m256i);
  __m256i least_12_bits_shifted_up = libcrux_intrinsics_avx2_mm256_slli_epi64(
      (int32_t)52, second_4_combined, __m256i);
  __m256i bits_sequential = libcrux_intrinsics_avx2_mm256_add_epi64(
      adjacent_4_combined1, least_12_bits_shifted_up);
  __m256i bits_sequential0 = libcrux_intrinsics_avx2_mm256_srlv_epi64(
      bits_sequential, libcrux_intrinsics_avx2_mm256_set_epi64x(
                           (int64_t)0, (int64_t)0, (int64_t)12, (int64_t)0));
  __m128i bits_sequential1 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(bits_sequential0);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t),
      bits_sequential1);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)13U, uint8_t),
      uint8_t);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_t0_serialize_22(
    __m256i *simd_unit, Eurydice_slice out) {
  libcrux_ml_dsa_simd_avx2_encoding_t0_serialize(simd_unit, out);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_T0_DESERIALIZE_COEFFICIENT_MASK \
  (((int32_t)1 << 13U) - (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_t0_deserialize(
    Eurydice_slice serialized, __m256i *out) {
  uint8_t serialized_extended[16U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(serialized_extended, (size_t)0U, (size_t)13U,
                                  uint8_t),
      serialized, uint8_t);
  __m128i serialized0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, serialized_extended, uint8_t));
  __m256i serialized1 =
      libcrux_intrinsics_avx2_mm256_set_m128i(serialized0, serialized0);
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      serialized1,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)-1,
          (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)-1, (int8_t)-1, (int8_t)9,
          (int8_t)8, (int8_t)-1, (int8_t)8, (int8_t)7, (int8_t)6, (int8_t)-1,
          (int8_t)6, (int8_t)5, (int8_t)4, (int8_t)-1, (int8_t)-1, (int8_t)4,
          (int8_t)3, (int8_t)-1, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)-1,
          (int8_t)-1, (int8_t)1, (int8_t)0));
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi32(
                        (int32_t)3, (int32_t)6, (int32_t)1, (int32_t)4,
                        (int32_t)7, (int32_t)2, (int32_t)5, (int32_t)0));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients0,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_T0_DESERIALIZE_COEFFICIENT_MASK));
  out[0U] =
      libcrux_ml_dsa_simd_avx2_encoding_t0_change_interval(&coefficients1);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_t0_deserialize_22(
    Eurydice_slice serialized, __m256i *out) {
  libcrux_ml_dsa_simd_avx2_encoding_t0_deserialize(serialized, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_t1_serialize(
    __m256i *simd_unit, Eurydice_slice out) {
  uint8_t serialized[24U] = {0U};
  __m256i adjacent_2_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      simd_unit[0U], libcrux_intrinsics_avx2_mm256_set_epi32(
                         (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22,
                         (int32_t)0, (int32_t)22, (int32_t)0, (int32_t)22));
  __m256i adjacent_2_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)22, adjacent_2_combined, __m256i);
  __m256i adjacent_4_combined =
      libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
          adjacent_2_combined0,
          libcrux_intrinsics_avx2_mm256_set_epi32(
              (int32_t)0, (int32_t)0, (int32_t)6, (int32_t)4, (int32_t)0,
              (int32_t)0, (int32_t)2, (int32_t)0));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_4_combined,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12, (int32_t)0,
          (int32_t)12, (int32_t)0, (int32_t)12));
  __m256i adjacent_4_combined1 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)12, adjacent_4_combined0, __m256i);
  __m128i lower_4 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_4_combined1);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)16U, uint8_t),
      lower_4);
  __m128i upper_4 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_4_combined1, __m128i);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice2(serialized, (size_t)5U, (size_t)21U, uint8_t),
      upper_4);
  Eurydice_slice uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(serialized, (size_t)0U, (size_t)10U, uint8_t),
      uint8_t);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_t1_serialize_22(
    __m256i *simd_unit, Eurydice_slice out) {
  libcrux_ml_dsa_simd_avx2_encoding_t1_serialize(simd_unit, out);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_T1_DESERIALIZE_COEFFICIENT_MASK \
  (((int32_t)1 << 10U) - (int32_t)1)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_encoding_t1_deserialize(
    Eurydice_slice bytes, __m256i *out) {
  uint8_t bytes_extended[16U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_subslice2(bytes_extended, (size_t)0U,
                                                  (size_t)10U, uint8_t),
                      bytes, uint8_t);
  __m128i bytes_loaded = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, bytes_extended, uint8_t));
  __m256i bytes_loaded0 =
      libcrux_intrinsics_avx2_mm256_set_m128i(bytes_loaded, bytes_loaded);
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      bytes_loaded0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)9, (int8_t)8, (int8_t)-1, (int8_t)-1,
          (int8_t)8, (int8_t)7, (int8_t)-1, (int8_t)-1, (int8_t)7, (int8_t)6,
          (int8_t)-1, (int8_t)-1, (int8_t)6, (int8_t)5, (int8_t)-1, (int8_t)-1,
          (int8_t)4, (int8_t)3, (int8_t)-1, (int8_t)-1, (int8_t)3, (int8_t)2,
          (int8_t)-1, (int8_t)-1, (int8_t)2, (int8_t)1, (int8_t)-1, (int8_t)-1,
          (int8_t)1, (int8_t)0));
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_srlv_epi32(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi32(
                        (int32_t)6, (int32_t)4, (int32_t)2, (int32_t)0,
                        (int32_t)6, (int32_t)4, (int32_t)2, (int32_t)0));
  out[0U] = libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients0,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          LIBCRUX_ML_DSA_SIMD_AVX2_ENCODING_T1_DESERIALIZE_COEFFICIENT_MASK));
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_t1_deserialize_22(
    Eurydice_slice serialized, __m256i *out) {
  libcrux_ml_dsa_simd_avx2_encoding_t1_deserialize(serialized, out);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7 \
  ((size_t)2U * LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT)

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
    __m256i *re, size_t index, __m256i zeta, size_t step_by,
    __m256i field_modulus, __m256i inverse_of_modulus_mod_montgomery_r) {
  __m256i prod02 =
      libcrux_intrinsics_avx2_mm256_mul_epi32(re[index + step_by], zeta);
  __m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245,
                                                  re[index + step_by], __m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, zeta, __m256i));
  __m256i k02 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod02, inverse_of_modulus_mod_montgomery_r);
  __m256i k13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod13, inverse_of_modulus_mod_montgomery_r);
  __m256i c02 = libcrux_intrinsics_avx2_mm256_mul_epi32(k02, field_modulus);
  __m256i c13 = libcrux_intrinsics_avx2_mm256_mul_epi32(k13, field_modulus);
  __m256i res02 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod02, c02);
  __m256i res13 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod13, c13);
  __m256i res02_shifted =
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, res02, __m256i);
  __m256i t = libcrux_intrinsics_avx2_mm256_blend_epi32(
      (int32_t)170, res02_shifted, res13, __m256i);
  re[index + step_by] = re[index];
  libcrux_ml_dsa_simd_avx2_arithmetic_subtract(&re[index + step_by], &t);
  libcrux_ml_dsa_simd_avx2_arithmetic_add(&re[index], &t);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6 \
  (((size_t)1U << 6U) / LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT)

/**
 This is equivalent to the pqclean 0 and 1

 This does 32 Montgomery multiplications (192 multiplications).
 This is the same as in pqclean. The only difference is locality of registers.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6(
    __m256i *re) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  __m256i inverse_of_modulus_mod_montgomery_r =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R);
  __m256i zeta7 = libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)25847);
  __m256i zeta60 = libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)-2608894);
  __m256i zeta61 = libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)-518909);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)1U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)2U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)3U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)8U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)8U + (size_t)1U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)8U + (size_t)2U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)8U + (size_t)3U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)1U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)2U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)0U + (size_t)3U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)16U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)16U + (size_t)1U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)16U + (size_t)2U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)16U + (size_t)3U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)1U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)2U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)3U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)12U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)12U + (size_t)1U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)12U + (size_t)2U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)12U + (size_t)3U, zeta7,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_7,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)1U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)2U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)4U + (size_t)3U, zeta60,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)20U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)20U + (size_t)1U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)20U + (size_t)2U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6_mul(
      re, (size_t)20U + (size_t)3U, zeta61,
      LIBCRUX_ML_DSA_SIMD_AVX2_NTT_NTT_AT_LAYER_7_AND_6_STEP_BY_6,
      field_modulus, inverse_of_modulus_mod_montgomery_r);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.ntt.ntt_at_layer_5_to_3.round
with const generics
- STEP= 32
- STEP_BY= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_f6(__m256i *re,
                                                          size_t index,
                                                          int32_t zeta) {
  __m256i rhs = libcrux_intrinsics_avx2_mm256_set1_epi32(zeta);
  size_t offset = index * (size_t)32U * (size_t)2U /
                  LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT;
  for (size_t i = offset; i < offset + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&re[j + (size_t)4U],
                                                            &rhs);
    __m256i tmp =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j], re[j + (size_t)4U]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)4U]);
    re[j + (size_t)4U] = tmp;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.ntt.ntt_at_layer_5_to_3.round
with const generics
- STEP= 16
- STEP_BY= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(__m256i *re,
                                                          size_t index,
                                                          int32_t zeta) {
  __m256i rhs = libcrux_intrinsics_avx2_mm256_set1_epi32(zeta);
  size_t offset = index * (size_t)16U * (size_t)2U /
                  LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT;
  for (size_t i = offset; i < offset + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&re[j + (size_t)2U],
                                                            &rhs);
    __m256i tmp =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j], re[j + (size_t)2U]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] = tmp;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.ntt.ntt_at_layer_5_to_3.round
with const generics
- STEP= 8
- STEP_BY= 1
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(__m256i *re,
                                                          size_t index,
                                                          int32_t zeta) {
  __m256i rhs = libcrux_intrinsics_avx2_mm256_set1_epi32(zeta);
  size_t offset = index * (size_t)8U * (size_t)2U /
                  LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT;
  for (size_t i = offset; i < offset + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&re[j + (size_t)1U],
                                                            &rhs);
    __m256i tmp =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j], re[j + (size_t)1U]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] = tmp;
  }
}

/**
 Layer 5, 4, 3

 Each layer does 16 Montgomery multiplications -> 3*16 = 48 total
 pqclean does 4 * 4 on each layer -> 48 total | plus 4 * 4 shuffles every time
 (48)
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_f6(re, (size_t)0U,
                                                            (int32_t)237124);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_f6(re, (size_t)1U,
                                                            (int32_t)-777960);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_f6(re, (size_t)2U,
                                                            (int32_t)-876248);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_f6(re, (size_t)3U,
                                                            (int32_t)466468);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)0U,
                                                            (int32_t)1826347);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)1U,
                                                            (int32_t)2353451);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)2U,
                                                            (int32_t)-359251);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)3U,
                                                            (int32_t)-2091905);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)4U,
                                                            (int32_t)3119733);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)5U,
                                                            (int32_t)-2884855);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)6U,
                                                            (int32_t)3111497);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_90(re, (size_t)7U,
                                                            (int32_t)2680103);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)0U,
                                                            (int32_t)2725464);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)1U,
                                                            (int32_t)1024112);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)2U,
                                                            (int32_t)-1079900);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)3U,
                                                            (int32_t)3585928);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)4U,
                                                            (int32_t)-549488);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)5U,
                                                            (int32_t)-1119584);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)6U,
                                                            (int32_t)2619752);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)7U,
                                                            (int32_t)-2108549);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)8U,
                                                            (int32_t)-2118186);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)9U,
                                                            (int32_t)-3859737);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)10U,
                                                            (int32_t)-1399561);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)11U,
                                                            (int32_t)-3277672);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)12U,
                                                            (int32_t)1757237);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)13U,
                                                            (int32_t)-19422);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)14U,
                                                            (int32_t)4010497);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3_round_7b(re, (size_t)15U,
                                                            (int32_t)280005);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(
    __m256i *re, size_t index, int32_t zeta0, int32_t zeta1) {
  __m256i summands = libcrux_intrinsics_avx2_mm256_set_m128i(
      libcrux_intrinsics_avx2_mm256_castsi256_si128(re[index + (size_t)1U]),
      libcrux_intrinsics_avx2_mm256_castsi256_si128(re[index]));
  __m256i zeta_products = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)19, re[index + (size_t)1U], re[index], __m256i);
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta1, zeta1, zeta1, zeta1, zeta0, zeta0, zeta0, zeta0);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&zeta_products,
                                                          &zetas);
  __m256i sub_terms =
      libcrux_intrinsics_avx2_mm256_sub_epi32(summands, zeta_products);
  __m256i add_terms =
      libcrux_intrinsics_avx2_mm256_add_epi32(summands, zeta_products);
  re[index] = libcrux_intrinsics_avx2_mm256_set_m128i(
      libcrux_intrinsics_avx2_mm256_castsi256_si128(sub_terms),
      libcrux_intrinsics_avx2_mm256_castsi256_si128(add_terms));
  re[index + (size_t)1U] = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)19, sub_terms, add_terms, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_2(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)0U, (int32_t)2706023,
                                           (int32_t)95776);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)2U, (int32_t)3077325,
                                           (int32_t)3530437);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)4U, (int32_t)-1661693,
                                           (int32_t)-3592148);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)6U, (int32_t)-2537516,
                                           (int32_t)3915439);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)8U, (int32_t)-3861115,
                                           (int32_t)-3043716);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)10U, (int32_t)3574422,
                                           (int32_t)-2867647);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)12U, (int32_t)3539968,
                                           (int32_t)-300467);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)14U, (int32_t)2348700,
                                           (int32_t)-539299);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)16U, (int32_t)-1699267,
                                           (int32_t)-1643818);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)18U, (int32_t)3505694,
                                           (int32_t)-3821735);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)20U, (int32_t)3507263,
                                           (int32_t)-2140649);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)22U, (int32_t)-1600420,
                                           (int32_t)3699596);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)24U, (int32_t)811944,
                                           (int32_t)531354);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)26U, (int32_t)954230,
                                           (int32_t)3881043);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)28U, (int32_t)3900724,
                                           (int32_t)-2556880);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_8(re, (size_t)30U, (int32_t)2071892,
                                           (int32_t)-2797779);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(
    __m256i *re, size_t index, int32_t zeta_a0, int32_t zeta_a1,
    int32_t zeta_b0, int32_t zeta_b1) {
  __m256i summands = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(
      re[index], re[index + (size_t)1U]);
  __m256i zeta_products = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(
      re[index], re[index + (size_t)1U]);
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta_b1, zeta_b1, zeta_a1, zeta_a1, zeta_b0, zeta_b0, zeta_a0, zeta_a0);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&zeta_products,
                                                          &zetas);
  __m256i sub_terms =
      libcrux_intrinsics_avx2_mm256_sub_epi32(summands, zeta_products);
  __m256i add_terms =
      libcrux_intrinsics_avx2_mm256_add_epi32(summands, zeta_products);
  re[index] =
      libcrux_intrinsics_avx2_mm256_unpacklo_epi64(add_terms, sub_terms);
  re[index + (size_t)1U] =
      libcrux_intrinsics_avx2_mm256_unpackhi_epi64(add_terms, sub_terms);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_1(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)0U, (int32_t)-3930395,
                                           (int32_t)-1528703, (int32_t)-3677745,
                                           (int32_t)-3041255);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)2U, (int32_t)-1452451,
                                           (int32_t)3475950, (int32_t)2176455,
                                           (int32_t)-1585221);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)4U, (int32_t)-1257611,
                                           (int32_t)1939314, (int32_t)-4083598,
                                           (int32_t)-1000202);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)6U, (int32_t)-3190144,
                                           (int32_t)-3157330, (int32_t)-3632928,
                                           (int32_t)126922);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)8U, (int32_t)3412210,
                                           (int32_t)-983419, (int32_t)2147896,
                                           (int32_t)2715295);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)10U, (int32_t)-2967645,
                                           (int32_t)-3693493, (int32_t)-411027,
                                           (int32_t)-2477047);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)12U, (int32_t)-671102,
                                           (int32_t)-1228525, (int32_t)-22981,
                                           (int32_t)-1308169);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)14U, (int32_t)-381987,
                                           (int32_t)1349076, (int32_t)1852771,
                                           (int32_t)-1430430);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)16U, (int32_t)-3343383,
                                           (int32_t)264944, (int32_t)508951,
                                           (int32_t)3097992);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)18U, (int32_t)44288,
                                           (int32_t)-1100098, (int32_t)904516,
                                           (int32_t)3958618);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)20U, (int32_t)-3724342,
                                           (int32_t)-8578, (int32_t)1653064,
                                           (int32_t)-3249728);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)22U, (int32_t)2389356,
                                           (int32_t)-210977, (int32_t)759969,
                                           (int32_t)-1316856);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)24U, (int32_t)189548,
                                           (int32_t)-3553272, (int32_t)3159746,
                                           (int32_t)-1851402);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)26U, (int32_t)-2409325,
                                           (int32_t)-177440, (int32_t)1315589,
                                           (int32_t)1341330);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)28U, (int32_t)1285669,
                                           (int32_t)-1584928, (int32_t)-812732,
                                           (int32_t)-1439742);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_4(re, (size_t)30U, (int32_t)-3019102,
                                           (int32_t)-3881060, (int32_t)-3628969,
                                           (int32_t)3839961);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
    __m256i *re, size_t index, int32_t zeta_a0, int32_t zeta_a1,
    int32_t zeta_a2, int32_t zeta_a3, int32_t zeta_b0, int32_t zeta_b1,
    int32_t zeta_b2, int32_t zeta_b3) {
  __m256i a = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)216,
                                                          re[index], __m256i);
  __m256i b = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)216, re[index + (size_t)1U], __m256i);
  __m256i summands = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(a, b);
  __m256i zeta_products = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(a, b);
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta_b3, zeta_b2, zeta_a3, zeta_a2, zeta_b1, zeta_b0, zeta_a1, zeta_a0);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&zeta_products,
                                                          &zetas);
  __m256i sub_terms =
      libcrux_intrinsics_avx2_mm256_sub_epi32(summands, zeta_products);
  __m256i add_terms =
      libcrux_intrinsics_avx2_mm256_add_epi32(summands, zeta_products);
  __m256i a_terms_shuffled =
      libcrux_intrinsics_avx2_mm256_unpacklo_epi64(add_terms, sub_terms);
  __m256i b_terms_shuffled =
      libcrux_intrinsics_avx2_mm256_unpackhi_epi64(add_terms, sub_terms);
  re[index] = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)216, a_terms_shuffled, __m256i);
  re[index + (size_t)1U] = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)216, b_terms_shuffled, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_0(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)0U, (int32_t)2091667, (int32_t)3407706, (int32_t)2316500,
      (int32_t)3817976, (int32_t)-3342478, (int32_t)2244091, (int32_t)-2446433,
      (int32_t)-3562462);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)2U, (int32_t)266997, (int32_t)2434439, (int32_t)-1235728,
      (int32_t)3513181, (int32_t)-3520352, (int32_t)-3759364, (int32_t)-1197226,
      (int32_t)-3193378);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)4U, (int32_t)900702, (int32_t)1859098, (int32_t)909542,
      (int32_t)819034, (int32_t)495491, (int32_t)-1613174, (int32_t)-43260,
      (int32_t)-522500);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)6U, (int32_t)-655327, (int32_t)-3122442, (int32_t)2031748,
      (int32_t)3207046, (int32_t)-3556995, (int32_t)-525098, (int32_t)-768622,
      (int32_t)-3595838);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)8U, (int32_t)342297, (int32_t)286988, (int32_t)-2437823,
      (int32_t)4108315, (int32_t)3437287, (int32_t)-3342277, (int32_t)1735879,
      (int32_t)203044);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)10U, (int32_t)2842341, (int32_t)2691481, (int32_t)-2590150,
      (int32_t)1265009, (int32_t)4055324, (int32_t)1247620, (int32_t)2486353,
      (int32_t)1595974);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)12U, (int32_t)-3767016, (int32_t)1250494, (int32_t)2635921,
      (int32_t)-3548272, (int32_t)-2994039, (int32_t)1869119, (int32_t)1903435,
      (int32_t)-1050970);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)14U, (int32_t)-1333058, (int32_t)1237275, (int32_t)-3318210,
      (int32_t)-1430225, (int32_t)-451100, (int32_t)1312455, (int32_t)3306115,
      (int32_t)-1962642);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)16U, (int32_t)-1279661, (int32_t)1917081, (int32_t)-2546312,
      (int32_t)-1374803, (int32_t)1500165, (int32_t)777191, (int32_t)2235880,
      (int32_t)3406031);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)18U, (int32_t)-542412, (int32_t)-2831860, (int32_t)-1671176,
      (int32_t)-1846953, (int32_t)-2584293, (int32_t)-3724270, (int32_t)594136,
      (int32_t)-3776993);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)20U, (int32_t)-2013608, (int32_t)2432395, (int32_t)2454455,
      (int32_t)-164721, (int32_t)1957272, (int32_t)3369112, (int32_t)185531,
      (int32_t)-1207385);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)22U, (int32_t)-3183426, (int32_t)162844, (int32_t)1616392,
      (int32_t)3014001, (int32_t)810149, (int32_t)1652634, (int32_t)-3694233,
      (int32_t)-1799107);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)24U, (int32_t)-3038916, (int32_t)3523897, (int32_t)3866901,
      (int32_t)269760, (int32_t)2213111, (int32_t)-975884, (int32_t)1717735,
      (int32_t)472078);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)26U, (int32_t)-426683, (int32_t)1723600, (int32_t)-1803090,
      (int32_t)1910376, (int32_t)-1667432, (int32_t)-1104333, (int32_t)-260646,
      (int32_t)-3833893);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)28U, (int32_t)-2939036, (int32_t)-2235985, (int32_t)-420899,
      (int32_t)-2286327, (int32_t)183443, (int32_t)-976891, (int32_t)1612842,
      (int32_t)-3545687);
  libcrux_ml_dsa_simd_avx2_ntt_butterfly_2(
      re, (size_t)30U, (int32_t)-554416, (int32_t)3919660, (int32_t)-48306,
      (int32_t)-1362209, (int32_t)3937738, (int32_t)1400424, (int32_t)-846154,
      (int32_t)1976782);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_ntt_ntt_avx2_ntt(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_7_and_6(re);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_5_to_3(re);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_2(re);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_1(re);
  libcrux_ml_dsa_simd_avx2_ntt_ntt_at_layer_0(re);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_ntt_ntt(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_ntt_ntt_avx2_ntt(re);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_ntt_22(
    __m256i *simd_units) {
  libcrux_ml_dsa_simd_avx2_ntt_ntt(simd_units);
}

typedef struct libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2_s {
  __m256i fst;
  __m256i snd;
} libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2
libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_0(
    __m256i simd_unit0, __m256i simd_unit1, int32_t zeta00, int32_t zeta01,
    int32_t zeta02, int32_t zeta03, int32_t zeta10, int32_t zeta11,
    int32_t zeta12, int32_t zeta13) {
  __m256i a_shuffled = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)216, simd_unit0, __m256i);
  __m256i b_shuffled0 = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)216, simd_unit1, __m256i);
  __m256i lo_values =
      libcrux_intrinsics_avx2_mm256_unpacklo_epi64(a_shuffled, b_shuffled0);
  __m256i hi_values =
      libcrux_intrinsics_avx2_mm256_unpackhi_epi64(a_shuffled, b_shuffled0);
  __m256i differences = hi_values;
  libcrux_ml_dsa_simd_avx2_arithmetic_subtract(&differences, &lo_values);
  libcrux_ml_dsa_simd_avx2_arithmetic_add(&lo_values, &hi_values);
  __m256i sums = lo_values;
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta13, zeta12, zeta03, zeta02, zeta11, zeta10, zeta01, zeta00);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&differences, &zetas);
  __m256i a_shuffled0 =
      libcrux_intrinsics_avx2_mm256_unpacklo_epi64(sums, differences);
  __m256i b_shuffled =
      libcrux_intrinsics_avx2_mm256_unpackhi_epi64(sums, differences);
  __m256i a = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)216,
                                                          a_shuffled0, __m256i);
  __m256i b = libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)216,
                                                          b_shuffled, __m256i);
  return (CLITERAL(libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2){.fst = a,
                                                                   .snd = b});
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
    __m256i *re, size_t index, int32_t zeta00, int32_t zeta01, int32_t zeta02,
    int32_t zeta03, int32_t zeta10, int32_t zeta11, int32_t zeta12,
    int32_t zeta13) {
  libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2 uu____0 =
      libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_0(
          re[index], re[index + (size_t)1U], zeta00, zeta01, zeta02, zeta03,
          zeta10, zeta11, zeta12, zeta13);
  __m256i lhs0 = uu____0.fst;
  __m256i lhs = uu____0.snd;
  re[index] = lhs0;
  re[index + (size_t)1U] = lhs;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)0U, (int32_t)1976782, (int32_t)-846154, (int32_t)1400424,
      (int32_t)3937738, (int32_t)-1362209, (int32_t)-48306, (int32_t)3919660,
      (int32_t)-554416);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)2U, (int32_t)-3545687, (int32_t)1612842, (int32_t)-976891,
      (int32_t)183443, (int32_t)-2286327, (int32_t)-420899, (int32_t)-2235985,
      (int32_t)-2939036);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)4U, (int32_t)-3833893, (int32_t)-260646, (int32_t)-1104333,
      (int32_t)-1667432, (int32_t)1910376, (int32_t)-1803090, (int32_t)1723600,
      (int32_t)-426683);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)6U, (int32_t)472078, (int32_t)1717735, (int32_t)-975884,
      (int32_t)2213111, (int32_t)269760, (int32_t)3866901, (int32_t)3523897,
      (int32_t)-3038916);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)8U, (int32_t)-1799107, (int32_t)-3694233, (int32_t)1652634,
      (int32_t)810149, (int32_t)3014001, (int32_t)1616392, (int32_t)162844,
      (int32_t)-3183426);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)10U, (int32_t)-1207385, (int32_t)185531, (int32_t)3369112,
      (int32_t)1957272, (int32_t)-164721, (int32_t)2454455, (int32_t)2432395,
      (int32_t)-2013608);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)12U, (int32_t)-3776993, (int32_t)594136, (int32_t)-3724270,
      (int32_t)-2584293, (int32_t)-1846953, (int32_t)-1671176,
      (int32_t)-2831860, (int32_t)-542412);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)14U, (int32_t)3406031, (int32_t)2235880, (int32_t)777191,
      (int32_t)1500165, (int32_t)-1374803, (int32_t)-2546312, (int32_t)1917081,
      (int32_t)-1279661);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)16U, (int32_t)-1962642, (int32_t)3306115, (int32_t)1312455,
      (int32_t)-451100, (int32_t)-1430225, (int32_t)-3318210, (int32_t)1237275,
      (int32_t)-1333058);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)18U, (int32_t)-1050970, (int32_t)1903435, (int32_t)1869119,
      (int32_t)-2994039, (int32_t)-3548272, (int32_t)2635921, (int32_t)1250494,
      (int32_t)-3767016);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)20U, (int32_t)1595974, (int32_t)2486353, (int32_t)1247620,
      (int32_t)4055324, (int32_t)1265009, (int32_t)-2590150, (int32_t)2691481,
      (int32_t)2842341);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)22U, (int32_t)203044, (int32_t)1735879, (int32_t)-3342277,
      (int32_t)3437287, (int32_t)4108315, (int32_t)-2437823, (int32_t)286988,
      (int32_t)342297);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)24U, (int32_t)-3595838, (int32_t)-768622, (int32_t)-525098,
      (int32_t)-3556995, (int32_t)3207046, (int32_t)2031748, (int32_t)-3122442,
      (int32_t)-655327);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)26U, (int32_t)-522500, (int32_t)-43260, (int32_t)-1613174,
      (int32_t)495491, (int32_t)819034, (int32_t)909542, (int32_t)1859098,
      (int32_t)900702);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)28U, (int32_t)-3193378, (int32_t)-1197226, (int32_t)-3759364,
      (int32_t)-3520352, (int32_t)3513181, (int32_t)-1235728, (int32_t)2434439,
      (int32_t)266997);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)30U, (int32_t)-3562462, (int32_t)-2446433, (int32_t)2244091,
      (int32_t)-3342478, (int32_t)3817976, (int32_t)2316500, (int32_t)3407706,
      (int32_t)2091667);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2
libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_1(
    __m256i simd_unit0, __m256i simd_unit1, int32_t zeta00, int32_t zeta01,
    int32_t zeta10, int32_t zeta11) {
  __m256i lo_values =
      libcrux_intrinsics_avx2_mm256_unpacklo_epi64(simd_unit0, simd_unit1);
  __m256i hi_values =
      libcrux_intrinsics_avx2_mm256_unpackhi_epi64(simd_unit0, simd_unit1);
  __m256i differences = hi_values;
  libcrux_ml_dsa_simd_avx2_arithmetic_subtract(&differences, &lo_values);
  libcrux_ml_dsa_simd_avx2_arithmetic_add(&lo_values, &hi_values);
  __m256i sums = lo_values;
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta11, zeta11, zeta01, zeta01, zeta10, zeta10, zeta00, zeta00);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&differences, &zetas);
  __m256i a = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(sums, differences);
  __m256i b = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(sums, differences);
  return (CLITERAL(libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2){.fst = a,
                                                                   .snd = b});
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
    __m256i *re, size_t index, int32_t zeta_00, int32_t zeta_01,
    int32_t zeta_10, int32_t zeta_11) {
  libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2 uu____0 =
      libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_1(
          re[index], re[index + (size_t)1U], zeta_00, zeta_01, zeta_10,
          zeta_11);
  __m256i lhs0 = uu____0.fst;
  __m256i lhs = uu____0.snd;
  re[index] = lhs0;
  re[index + (size_t)1U] = lhs;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)0U, (int32_t)3839961, (int32_t)-3628969, (int32_t)-3881060,
      (int32_t)-3019102);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)2U, (int32_t)-1439742, (int32_t)-812732, (int32_t)-1584928,
      (int32_t)1285669);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)4U, (int32_t)1341330, (int32_t)1315589, (int32_t)-177440,
      (int32_t)-2409325);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)6U, (int32_t)-1851402, (int32_t)3159746, (int32_t)-3553272,
      (int32_t)189548);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)8U, (int32_t)-1316856, (int32_t)759969, (int32_t)-210977,
      (int32_t)2389356);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)10U, (int32_t)-3249728, (int32_t)1653064, (int32_t)-8578,
      (int32_t)-3724342);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)12U, (int32_t)3958618, (int32_t)904516, (int32_t)-1100098,
      (int32_t)44288);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)14U, (int32_t)3097992, (int32_t)508951, (int32_t)264944,
      (int32_t)-3343383);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)16U, (int32_t)-1430430, (int32_t)1852771, (int32_t)1349076,
      (int32_t)-381987);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)18U, (int32_t)-1308169, (int32_t)-22981, (int32_t)-1228525,
      (int32_t)-671102);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)20U, (int32_t)-2477047, (int32_t)-411027, (int32_t)-3693493,
      (int32_t)-2967645);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)22U, (int32_t)2715295, (int32_t)2147896, (int32_t)-983419,
      (int32_t)3412210);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)24U, (int32_t)126922, (int32_t)-3632928, (int32_t)-3157330,
      (int32_t)-3190144);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)26U, (int32_t)-1000202, (int32_t)-4083598, (int32_t)1939314,
      (int32_t)-1257611);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)28U, (int32_t)-1585221, (int32_t)2176455, (int32_t)3475950,
      (int32_t)-1452451);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)30U, (int32_t)-3041255, (int32_t)-3677745, (int32_t)-1528703,
      (int32_t)-3930395);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2
libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_2(
    __m256i simd_unit0, __m256i simd_unit1, int32_t zeta0, int32_t zeta1) {
  __m256i lo_values = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)32, simd_unit0, simd_unit1, __m256i);
  __m256i hi_values = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)49, simd_unit0, simd_unit1, __m256i);
  __m256i differences = hi_values;
  libcrux_ml_dsa_simd_avx2_arithmetic_subtract(&differences, &lo_values);
  libcrux_ml_dsa_simd_avx2_arithmetic_add(&lo_values, &hi_values);
  __m256i sums = lo_values;
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi32(
      zeta1, zeta1, zeta1, zeta1, zeta0, zeta0, zeta0, zeta0);
  libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply(&differences, &zetas);
  __m256i a = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)32, sums, differences, __m256i);
  __m256i b = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
      (int32_t)49, sums, differences, __m256i);
  return (CLITERAL(libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2){.fst = a,
                                                                   .snd = b});
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(__m256i *re,
                                                            size_t index,
                                                            int32_t zeta1,
                                                            int32_t zeta2) {
  libcrux_ml_dsa_simd_avx2_vector_type_Vec256_x2 uu____0 =
      libcrux_ml_dsa_simd_avx2_invntt_simd_unit_invert_ntt_at_layer_2(
          re[index], re[index + (size_t)1U], zeta1, zeta2);
  __m256i lhs0 = uu____0.fst;
  __m256i lhs = uu____0.snd;
  re[index] = lhs0;
  re[index + (size_t)1U] = lhs;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)0U, (int32_t)-2797779, (int32_t)2071892);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)2U, (int32_t)-2556880, (int32_t)3900724);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)4U, (int32_t)3881043, (int32_t)954230);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)6U, (int32_t)531354, (int32_t)811944);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)8U, (int32_t)3699596, (int32_t)-1600420);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)10U, (int32_t)-2140649, (int32_t)3507263);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)12U, (int32_t)-3821735, (int32_t)3505694);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)14U, (int32_t)-1643818, (int32_t)-1699267);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)16U, (int32_t)-539299, (int32_t)2348700);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)18U, (int32_t)-300467, (int32_t)3539968);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)20U, (int32_t)-2867647, (int32_t)3574422);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)22U, (int32_t)-3043716, (int32_t)-3861115);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)24U, (int32_t)3915439, (int32_t)-2537516);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)26U, (int32_t)-3592148, (int32_t)-1661693);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)28U, (int32_t)3530437, (int32_t)3077325);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)30U, (int32_t)95776, (int32_t)2706023);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i lhs, int32_t constant) {
  __m256i rhs = libcrux_intrinsics_avx2_mm256_set1_epi32(constant);
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  __m256i inverse_of_modulus_mod_montgomery_r =
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R);
  __m256i prod02 = libcrux_intrinsics_avx2_mm256_mul_epi32(lhs, rhs);
  __m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, lhs, __m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, rhs, __m256i));
  __m256i k02 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod02, inverse_of_modulus_mod_montgomery_r);
  __m256i k13 = libcrux_intrinsics_avx2_mm256_mul_epi32(
      prod13, inverse_of_modulus_mod_montgomery_r);
  __m256i c02 = libcrux_intrinsics_avx2_mm256_mul_epi32(k02, field_modulus);
  __m256i c13 = libcrux_intrinsics_avx2_mm256_mul_epi32(k13, field_modulus);
  __m256i res02 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod02, c02);
  __m256i res13 = libcrux_intrinsics_avx2_mm256_sub_epi32(prod13, c13);
  __m256i res02_shifted =
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, res02, __m256i);
  return libcrux_intrinsics_avx2_mm256_blend_epi32((int32_t)170, res02_shifted,
                                                   res13, __m256i);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_99(
    __m256i *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)280005);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_1c(
    __m256i *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)4010497);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_6b(
    __m256i *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-19422);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_44(
    __m256i *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1757237);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a8(
    __m256i *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-3277672);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_1f(
    __m256i *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1399561);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_95(
    __m256i *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-3859737);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b(
    __m256i *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2118186);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a(
    __m256i *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2108549);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_e4(
    __m256i *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2619752);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_de(
    __m256i *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1119584);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_05(
    __m256i *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-549488);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d9(
    __m256i *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3585928);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3a(
    __m256i *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1079900);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b0(
    __m256i *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1024112);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a0(
    __m256i *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)1U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)1U]);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2725464);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_3(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_99(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_1c(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_6b(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_44(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a8(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_1f(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_95(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_e4(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_de(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_05(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d9(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3a(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b0(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a0(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_990(
    __m256i *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2680103);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_6b0(
    __m256i *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3111497);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a80(
    __m256i *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2884855);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_950(
    __m256i *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3119733);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a0(
    __m256i *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2091905);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_de0(
    __m256i *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-359251);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d90(
    __m256i *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2353451);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b1(
    __m256i *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)2U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)2U]);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1826347);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_4(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_990(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_6b0(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a80(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_950(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a0(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_de0(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d90(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_3b1(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_991(
    __m256i *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)4U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)4U]);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)466468);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a81(
    __m256i *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)4U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)4U]);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-876248);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a1(
    __m256i *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)4U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)4U]);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-777960);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d91(
    __m256i *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)4U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)4U]);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)237124);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_5(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_991(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_a81(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a1(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_d91(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_992(
    __m256i *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)8U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)8U]);
    re[j + (size_t)8U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-518909);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a2(
    __m256i *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)8U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)8U]);
    re[j + (size_t)8U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2608894);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_6(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_992(re);
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_7a2(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_993(
    __m256i *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    __m256i a_minus_b =
        libcrux_intrinsics_avx2_mm256_sub_epi32(re[j + (size_t)16U], re[j]);
    re[j] = libcrux_intrinsics_avx2_mm256_add_epi32(re[j], re[j + (size_t)16U]);
    re[j + (size_t)16U] =
        libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)25847);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_7(
    __m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_outer_3_plus_993(re);
}

#define LIBCRUX_ML_DSA_SIMD_AVX2_INVNTT_INVERT_NTT_MONTGOMERY_INV_INNER_FACTOR \
  ((int32_t)41978)

KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_montgomery_inv_inner(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_0(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_1(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_2(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_3(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_4(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_5(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_6(re);
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_at_layer_7(re);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)32U, re, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    re[i0] = libcrux_ml_dsa_simd_avx2_arithmetic_montgomery_multiply_by_constant(
        re[i0],
        LIBCRUX_ML_DSA_SIMD_AVX2_INVNTT_INVERT_NTT_MONTGOMERY_INV_INNER_FACTOR);
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_montgomery(__m256i *re) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_montgomery_inv_inner(re);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_avx2_invert_ntt_montgomery_22(
    __m256i *simd_units) {
  libcrux_ml_dsa_simd_avx2_invntt_invert_ntt_montgomery(simd_units);
}

/**
A monomorphic instance of libcrux_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256

*/
typedef struct libcrux_ml_dsa_polynomial_PolynomialRingElement_4b_s {
  __m256i simd_units[32U];
} libcrux_ml_dsa_polynomial_PolynomialRingElement_4b;

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.zero_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_dsa_polynomial_PolynomialRingElement_4b
libcrux_ml_dsa_polynomial_zero_ff_21(void) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b lit;
  __m256i repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] = libcrux_ml_dsa_simd_avx2_zero_22();
  }
  memcpy(lit.simd_units, repeat_expression, (size_t)32U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)24U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes =
        Eurydice_slice_subslice2(randomness, _cloop_i * (size_t)24U,
                                 _cloop_i * (size_t)24U + (size_t)24U, uint8_t);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_field_modulus_22(
              uu____0, Eurydice_array_to_subslice_from((size_t)263U, out,
                                                       sampled_coefficients[0U],
                                                       int32_t, size_t));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.from_i32_array_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_polynomial_from_i32_array_ff_21(
    Eurydice_slice array,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_from_coefficient_array_22(
        Eurydice_slice_subslice2(
            array, i0 * LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            int32_t),
        &result->simd_units[i0]);
  }
}

/**
 Sample and write out up to four ring elements.

 If i <= `elements_requested`, a field element with domain separated
 seed according to the provided index is generated in
 `tmp_stack[i]`. After successful rejection sampling in
 `tmp_stack[i]`, the ring element is written to `matrix` at the
 provided index in `indices[i]`.
 `rand_stack` is a working buffer that holds initial Shake output.
*/
/**
A monomorphic instance of
libcrux_ml_dsa.sample.sample_up_to_four_ring_elements_flat with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_0a(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix,
    uint8_t *rand_stack0, uint8_t *rand_stack1, uint8_t *rand_stack2,
    uint8_t *rand_stack3, Eurydice_slice tmp_stack, size_t start_index,
    size_t elements_requested) {
  uint8_t seed0[34U];
  libcrux_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(start_index,
                                                                    columns),
      seed0);
  uint8_t seed1[34U];
  libcrux_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)1U, columns),
      seed1);
  uint8_t seed2[34U];
  libcrux_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)2U, columns),
      seed2);
  uint8_t seed3[34U];
  libcrux_ml_dsa_sample_add_domain_separator(
      seed,
      libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
          start_index + (size_t)3U, columns),
      seed3);
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
      libcrux_ml_dsa_hash_functions_simd256_init_absorb_7b(
          Eurydice_array_to_slice((size_t)34U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed3, uint8_t));
  libcrux_ml_dsa_hash_functions_simd256_squeeze_first_five_blocks_7b(
      &state, rand_stack0, rand_stack1, rand_stack2, rand_stack3);
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
          Eurydice_array_to_slice((size_t)840U, rand_stack0, uint8_t),
          &sampled0,
          Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done1 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
          Eurydice_array_to_slice((size_t)840U, rand_stack1, uint8_t),
          &sampled1,
          Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done2 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
          Eurydice_array_to_slice((size_t)840U, rand_stack2, uint8_t),
          &sampled2,
          Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                               int32_t(*)[263U]));
  bool done3 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
          Eurydice_array_to_slice((size_t)840U, rand_stack3, uint8_t),
          &sampled3,
          Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                               int32_t(*)[263U]));
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_168size_t__x4 randomnesses =
                libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_7b(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                              uint8_t),
                      &sampled0,
                      Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done1) {
              done1 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                              uint8_t),
                      &sampled1,
                      Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done2) {
              done2 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                              uint8_t),
                      &sampled2,
                      Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
            if (!done3) {
              done3 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                              uint8_t),
                      &sampled3,
                      Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                           int32_t(*)[263U]));
            }
          }
        } else {
          uint8_t_168size_t__x4 randomnesses =
              libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_7b(
                  &state);
          if (!done0) {
            done0 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                            uint8_t),
                    &sampled0,
                    Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done1) {
            done1 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                            uint8_t),
                    &sampled1,
                    Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done2) {
            done2 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                            uint8_t),
                    &sampled2,
                    Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
          if (!done3) {
            done3 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                            uint8_t),
                    &sampled3,
                    Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                         int32_t(*)[263U]));
          }
        }
      } else {
        uint8_t_168size_t__x4 randomnesses =
            libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_7b(&state);
        if (!done0) {
          done0 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                          uint8_t),
                  &sampled0,
                  Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done1) {
          done1 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                          uint8_t),
                  &sampled1,
                  Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done2) {
          done2 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                          uint8_t),
                  &sampled2,
                  Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
        if (!done3) {
          done3 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                          uint8_t),
                  &sampled3,
                  Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                       int32_t(*)[263U]));
        }
      }
    } else {
      uint8_t_168size_t__x4 randomnesses =
          libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_7b(&state);
      if (!done0) {
        done0 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                        uint8_t),
                &sampled0,
                Eurydice_slice_index(tmp_stack, (size_t)0U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done1) {
        done1 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                        uint8_t),
                &sampled1,
                Eurydice_slice_index(tmp_stack, (size_t)1U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done2) {
        done2 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                        uint8_t),
                &sampled2,
                Eurydice_slice_index(tmp_stack, (size_t)2U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
      if (!done3) {
        done3 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_21(
                Eurydice_array_to_slice((size_t)168U, randomnesses.f3, uint8_t),
                &sampled3,
                Eurydice_slice_index(tmp_stack, (size_t)3U, int32_t[263U],
                                     int32_t(*)[263U]));
      }
    }
  }
  for (size_t i = (size_t)0U; i < elements_requested; i++) {
    size_t k = i;
    libcrux_ml_dsa_polynomial_from_i32_array_ff_21(
        Eurydice_array_to_slice(
            (size_t)263U,
            Eurydice_slice_index(tmp_stack, k, int32_t[263U], int32_t(*)[263U]),
            int32_t),
        &Eurydice_slice_index(
            matrix, start_index + k,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.matrix_flat
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_matrix_flat_0a(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix) {
  uint8_t rand_stack0[840U] = {0U};
  uint8_t rand_stack1[840U] = {0U};
  uint8_t rand_stack2[840U] = {0U};
  uint8_t rand_stack3[840U] = {0U};
  int32_t tmp_stack[4U][263U];
  memset(tmp_stack[0U], 0U, 263U * sizeof(int32_t));
  memset(tmp_stack[1U], 0U, 263U * sizeof(int32_t));
  memset(tmp_stack[2U], 0U, 263U * sizeof(int32_t));
  int32_t repeat_expression[263U] = {0U};
  memcpy(tmp_stack[3U], repeat_expression, (size_t)263U * sizeof(int32_t));
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               matrix, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b) /
               (size_t)4U;
       i++) {
    size_t start_index = i;
    size_t start_index0 = start_index * (size_t)4U;
    size_t uu____0 = start_index0 + (size_t)4U;
    size_t elements_requested;
    if (uu____0 <=
        Eurydice_slice_len(
            matrix, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b)) {
      elements_requested = (size_t)4U;
    } else {
      elements_requested =
          Eurydice_slice_len(
              matrix, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b) -
          start_index0;
    }
    libcrux_ml_dsa_sample_sample_up_to_four_ring_elements_flat_0a(
        columns, seed, matrix, rand_stack0, rand_stack1, rand_stack2,
        rand_stack3,
        Eurydice_array_to_slice((size_t)4U, tmp_stack, int32_t[263U]),
        start_index0, elements_requested);
  }
}

/**
This function found in impl {(libcrux_ml_dsa::samplex4::X4Sampler for
libcrux_ml_dsa::samplex4::avx2::AVX2Sampler)}
*/
/**
A monomorphic instance of libcrux_ml_dsa.samplex4.avx2.matrix_flat.inner_b8
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_samplex4_avx2_matrix_flat_inner_b8_21(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix) {
  libcrux_ml_dsa_samplex4_matrix_flat_0a(columns, seed, matrix);
}

/**
This function found in impl {(libcrux_ml_dsa::samplex4::X4Sampler for
libcrux_ml_dsa::samplex4::avx2::AVX2Sampler)}
*/
/**
A monomorphic instance of libcrux_ml_dsa.samplex4.avx2.matrix_flat_b8
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_samplex4_avx2_matrix_flat_b8_21(
    size_t columns, Eurydice_slice seed, Eurydice_slice matrix) {
  libcrux_ml_dsa_samplex4_avx2_matrix_flat_inner_b8_21(columns, seed, matrix);
}

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_21(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes =
        Eurydice_slice_subslice2(randomness, _cloop_i * (size_t)4U,
                                 _cloop_i * (size_t)4U + (size_t)4U, uint8_t);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_equals_4_22(
              uu____0, Eurydice_array_to_subslice_from((size_t)263U, out,
                                                       sampled_coefficients[0U],
                                                       int32_t, size_t));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_21(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_slice random_bytes =
        Eurydice_slice_subslice2(randomness, _cloop_i * (size_t)4U,
                                 _cloop_i * (size_t)4U + (size_t)4U, uint8_t);
    if (!done) {
      Eurydice_slice uu____0 = random_bytes;
      size_t sampled =
          libcrux_ml_dsa_simd_avx2_rejection_sample_less_than_eta_equals_2_22(
              uu____0, Eurydice_array_to_subslice_from((size_t)263U, out,
                                                       sampled_coefficients[0U],
                                                       int32_t, size_t));
      sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.rejection_sample_less_than_eta
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice randomness,
    size_t *sampled, int32_t *out) {
  if (!(eta == libcrux_ml_dsa_constants_Eta_Two)) {
    return libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_21(
        randomness, sampled, out);
  }
  return libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_21(
      randomness, sampled, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_four_error_ring_elements
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_sample_sample_four_error_ring_elements_fc(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice seed, uint16_t start_index,
    Eurydice_slice re) {
  uint8_t seed0[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(seed, start_index, seed0);
  uint8_t seed1[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 1U, seed1);
  uint8_t seed2[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 2U, seed2);
  uint8_t seed3[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 3U, seed3);
  libcrux_sha3_avx2_x4_incremental_KeccakState state =
      libcrux_ml_dsa_hash_functions_simd256_init_absorb_x4_fb(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t));
  uint8_t_136size_t__x4 randomnesses0 =
      libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_x4_fb(&state);
  int32_t out[4U][263U] = {{0U}};
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.fst, uint8_t),
      &sampled0, out[0U]);
  bool done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.snd, uint8_t),
      &sampled1, out[1U]);
  bool done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.thd, uint8_t),
      &sampled2, out[2U]);
  bool done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
      eta, Eurydice_array_to_slice((size_t)136U, randomnesses0.f3, uint8_t),
      &sampled3, out[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_136size_t__x4 randomnesses =
                libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4_fb(
                    &state);
            if (!done0) {
              done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                  eta,
                  Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                          uint8_t),
                  &sampled0, out[0U]);
            }
            if (!done1) {
              done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                  eta,
                  Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                          uint8_t),
                  &sampled1, out[1U]);
            }
            if (!done2) {
              done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                  eta,
                  Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                          uint8_t),
                  &sampled2, out[2U]);
            }
            if (!done3) {
              done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                  eta,
                  Eurydice_array_to_slice((size_t)136U, randomnesses.f3,
                                          uint8_t),
                  &sampled3, out[3U]);
            }
          }
        } else {
          uint8_t_136size_t__x4 randomnesses =
              libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4_fb(
                  &state);
          if (!done0) {
            done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                        uint8_t),
                &sampled0, out[0U]);
          }
          if (!done1) {
            done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                        uint8_t),
                &sampled1, out[1U]);
          }
          if (!done2) {
            done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                        uint8_t),
                &sampled2, out[2U]);
          }
          if (!done3) {
            done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
                eta,
                Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
                &sampled3, out[3U]);
          }
        }
      } else {
        uint8_t_136size_t__x4 randomnesses =
            libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4_fb(
                &state);
        if (!done0) {
          done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
              &sampled0, out[0U]);
        }
        if (!done1) {
          done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
              &sampled1, out[1U]);
        }
        if (!done2) {
          done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
              &sampled2, out[2U]);
        }
        if (!done3) {
          done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
              eta,
              Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
              &sampled3, out[3U]);
        }
      }
    } else {
      uint8_t_136size_t__x4 randomnesses =
          libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_x4_fb(
              &state);
      if (!done0) {
        done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
            &sampled0, out[0U]);
      }
      if (!done1) {
        done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
            &sampled1, out[1U]);
      }
      if (!done2) {
        done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
            &sampled2, out[2U]);
      }
      if (!done3) {
        done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_21(
            eta,
            Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
            &sampled3, out[3U]);
      }
    }
  }
  size_t max0 = (size_t)start_index + (size_t)4U;
  size_t max;
  if (Eurydice_slice_len(
          re, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b) < max0) {
    max = Eurydice_slice_len(
        re, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
  } else {
    max = max0;
  }
  for (size_t i = (size_t)start_index; i < max; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_polynomial_from_i32_array_ff_21(
        Eurydice_array_to_slice((size_t)263U, out[i0 % (size_t)4U], int32_t),
        &Eurydice_slice_index(
            re, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_sample_s1_and_s2_fc(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice seed,
    Eurydice_slice s1_s2) {
  size_t len = Eurydice_slice_len(
      s1_s2, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
  for (size_t i = (size_t)0U; i < len / (size_t)4U; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_sample_sample_four_error_ring_elements_fc(
        eta, seed, 4U * (uint32_t)(uint16_t)i0, s1_s2);
  }
  size_t remainder = len % (size_t)4U;
  if (remainder != (size_t)0U) {
    libcrux_ml_dsa_sample_sample_four_error_ring_elements_fc(
        eta, seed, (uint16_t)(len - remainder), s1_s2);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.ntt.ntt
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_ntt_ntt_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re) {
  libcrux_ml_dsa_simd_avx2_ntt_22(re->simd_units);
}

/**
A monomorphic instance of libcrux_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *lhs,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, lhs->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_montgomery_multiply_22(&lhs->simd_units[i0],
                                                    &rhs->simd_units[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.add_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_polynomial_add_ff_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *self,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, self->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_add_22(&self->simd_units[i0],
                                    &rhs->simd_units[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_ntt_invert_ntt_montgomery_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re) {
  libcrux_ml_dsa_simd_avx2_invert_ntt_montgomery_22(re->simd_units);
}

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_ml_dsa.matrix.compute_as1_plus_s2
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_matrix_compute_as1_plus_s2_21(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice a_as_ntt,
    Eurydice_slice s1_ntt, Eurydice_slice s1_s2, Eurydice_slice result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b product =
          Eurydice_slice_index(
              a_as_ntt, i1 * columns_in_a + j,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
      libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
          &product,
          &Eurydice_slice_index(
              s1_ntt, j, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_polynomial_add_ff_21(
          &Eurydice_slice_index(
              result, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
          &product);
    }
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               result, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_ntt_invert_ntt_montgomery_21(&Eurydice_slice_index(
        result, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    libcrux_ml_dsa_polynomial_add_ff_21(
        &Eurydice_slice_index(
            result, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        &Eurydice_slice_index(
            s1_s2, columns_in_a + i0,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.power2round_vector
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_arithmetic_power2round_vector_21(
    Eurydice_slice t, Eurydice_slice t1) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                t, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(
             Eurydice_array_to_slice(
                 (size_t)32U,
                 Eurydice_slice_index(
                     t, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                     libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
                     .simd_units,
                 __m256i),
             __m256i);
         i++) {
      size_t j = i;
      libcrux_ml_dsa_simd_avx2_power2round_22(
          &Eurydice_slice_index(
               t, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          &Eurydice_slice_index(
               t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.t1.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_t1_serialize_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &re->simd_units[i0];
    libcrux_ml_dsa_simd_avx2_t1_serialize_22(
        simd_unit,
        Eurydice_slice_subslice2(
            serialized,
            i0 *
                LIBCRUX_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t));
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_verification_key_generate_serialized_21(
    Eurydice_slice seed, Eurydice_slice t1,
    Eurydice_slice verification_key_serialized) {
  Eurydice_slice_copy(Eurydice_slice_subslice2(
                          verification_key_serialized, (size_t)0U,
                          LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t),
                      seed, uint8_t);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               t1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *ring_element =
        &Eurydice_slice_index(
            t1, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
    size_t offset = LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
                    i0 * LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE;
    libcrux_ml_dsa_encoding_t1_serialize_21(
        ring_element,
        Eurydice_slice_subslice2(
            verification_key_serialized, offset,
            offset + LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            uint8_t));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_hash_functions_simd256_shake256_24(
    Eurydice_slice input, uint8_t *out) {
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)64U, out, uint8_t), input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_d9
with const generics
- OUTPUT_LENGTH= 64
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_d9_24(Eurydice_slice input,
                                                     uint8_t *out) {
  libcrux_ml_dsa_hash_functions_simd256_shake256_24(input, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.error.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_error_serialize_21(
    libcrux_ml_dsa_constants_Eta eta,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re,
    Eurydice_slice serialized) {
  size_t output_bytes_per_simd_unit =
      libcrux_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &re->simd_units[i0];
    libcrux_ml_dsa_simd_avx2_error_serialize_22(
        eta, simd_unit,
        Eurydice_slice_subslice2(serialized, i0 * output_bytes_per_simd_unit,
                                 (i0 + (size_t)1U) * output_bytes_per_simd_unit,
                                 uint8_t));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.t0.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_t0_serialize_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &re->simd_units[i0];
    libcrux_ml_dsa_simd_avx2_t0_serialize_22(
        simd_unit,
        Eurydice_slice_subslice2(
            serialized,
            i0 * LIBCRUX_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t));
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_signing_key_generate_serialized_18(
    libcrux_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_slice seed_matrix, Eurydice_slice seed_signing,
    Eurydice_slice verification_key, Eurydice_slice s1_2, Eurydice_slice t0,
    Eurydice_slice signing_key_serialized) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(
          signing_key_serialized, offset,
          offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t),
      seed_matrix, uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE;
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(
          signing_key_serialized, offset,
          offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE, uint8_t),
      seed_signing, uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE;
  uint8_t verification_key_hash[64U] = {0U};
  libcrux_ml_dsa_hash_functions_simd256_shake256_d9_24(verification_key,
                                                       verification_key_hash);
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(
          signing_key_serialized, offset,
          offset + LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH,
          uint8_t),
      Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
      uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               s1_2, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_encoding_error_serialize_21(
        eta,
        &Eurydice_slice_index(
            s1_2, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        Eurydice_slice_subslice2(signing_key_serialized, offset,
                                 offset + error_ring_element_size, uint8_t));
    offset = offset + error_ring_element_size;
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               t0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t _cloop_j = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *ring_element =
        &Eurydice_slice_index(
            t0, _cloop_j, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
    libcrux_ml_dsa_encoding_t0_serialize_21(
        ring_element,
        Eurydice_slice_subslice2(
            signing_key_serialized, offset,
            offset + LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
            uint8_t));
    offset = offset + LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.generate_key_pair with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_07(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  uint8_t seed_expanded0[128U] = {0U};
  libcrux_sha3_portable_incremental_Shake256Xof shake =
      libcrux_ml_dsa_hash_functions_portable_init_83();
  libcrux_ml_dsa_hash_functions_portable_absorb_83(
      &shake, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  uint8_t buf[2U] = {(uint8_t)LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
                     (uint8_t)LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A};
  libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
      &shake, Eurydice_array_to_slice((size_t)2U, buf, uint8_t));
  libcrux_ml_dsa_hash_functions_portable_squeeze_83(
      &shake, Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t),
      LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice seed_expanded = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_error_vectors = uu____1.fst;
  Eurydice_slice seed_for_signing = uu____1.snd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b a_as_ntt[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    a_as_ntt[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_samplex4_avx2_matrix_flat_b8_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)30U, a_as_ntt,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b s1_s2[11U];
  for (size_t i = (size_t)0U; i < (size_t)11U; i++) {
    s1_s2[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_samplex4_sample_s1_and_s2_fc(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ETA, seed_for_error_vectors,
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b t0[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    t0[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b s1_ntt[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    s1_ntt[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)5U, s1_ntt, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
  Eurydice_slice_copy(
      uu____2,
      Eurydice_array_to_subslice2(
          s1_s2, (size_t)0U, LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)5U, s1_ntt,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_ntt_ntt_21(&s1_ntt[i0]);
  }
  libcrux_ml_dsa_matrix_compute_as1_plus_s2_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      Eurydice_array_to_slice(
          (size_t)30U, a_as_ntt,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice(
          (size_t)5U, s1_ntt,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice(
          (size_t)6U, t0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b t1[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    t1[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_arithmetic_power2round_vector_21(
      Eurydice_array_to_slice(
          (size_t)6U, t0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice(
          (size_t)6U, t1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_encoding_verification_key_generate_serialized_21(
      seed_for_a,
      Eurydice_array_to_slice(
          (size_t)6U, t1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      verification_key);
  libcrux_ml_dsa_encoding_signing_key_generate_serialized_18(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing, verification_key,
      Eurydice_array_to_slice(
          (size_t)11U, s1_s2,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice(
          (size_t)6U, t0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      signing_key);
}

/**
 Key Generation.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_generate_key_pair__inner(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_07(
      copy_of_randomness, signing_key, verification_key);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_generate_key_pair(
    uint8_t randomness[32U], Eurydice_slice signing_key,
    Eurydice_slice verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_generate_key_pair__inner(
      copy_of_randomness, signing_key, verification_key);
}

/**
 Generate an ML-DSA-65 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_dsa_types_MLDSAKeyPair_06
libcrux_ml_dsa_ml_dsa_65_avx2_generate_key_pair(uint8_t randomness[32U]) {
  uint8_t signing_key[4032U] = {0U};
  uint8_t verification_key[1952U] = {0U};
  uint8_t uu____0[32U];
  memcpy(uu____0, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_generate_key_pair(
      uu____0, Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t),
      Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key[4032U];
  memcpy(copy_of_signing_key, signing_key, (size_t)4032U * sizeof(uint8_t));
  libcrux_ml_dsa_types_MLDSASigningKey_22 uu____2 =
      libcrux_ml_dsa_types_new_9b_09(copy_of_signing_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key[1952U];
  memcpy(copy_of_verification_key, verification_key,
         (size_t)1952U * sizeof(uint8_t));
  libcrux_ml_dsa_types_MLDSAKeyPair_06 lit;
  lit.signing_key = uu____2;
  lit.verification_key =
      libcrux_ml_dsa_types_new_66_97(copy_of_verification_key);
  return lit;
}

/**
 Generate an ML-DSA-65 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_ml_dsa_65_avx2_generate_key_pair_mut(
    uint8_t randomness[32U], uint8_t *signing_key, uint8_t *verification_key) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_generate_key_pair(
      copy_of_randomness,
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t),
      Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.error.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_error_deserialize_21(
    libcrux_ml_dsa_constants_Eta eta, Eurydice_slice serialized,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result) {
  size_t chunk_size = libcrux_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)32U, result->simd_units, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_error_deserialize_22(
        eta,
        Eurydice_slice_subslice2(serialized, i0 * chunk_size,
                                 (i0 + (size_t)1U) * chunk_size, uint8_t),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_21(
    libcrux_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_slice serialized, Eurydice_slice ring_elements) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / ring_element_size; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * ring_element_size,
        i0 * ring_element_size + ring_element_size, uint8_t);
    libcrux_ml_dsa_encoding_error_deserialize_21(
        eta, bytes,
        &Eurydice_slice_index(
            ring_elements, i0,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    libcrux_ml_dsa_ntt_ntt_21(&Eurydice_slice_index(
        ring_elements, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.t0.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_t0_deserialize_21(
    Eurydice_slice serialized,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)32U, result->simd_units, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_t0_deserialize_22(
        Eurydice_slice_subslice2(
            serialized,
            i0 * LIBCRUX_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
            uint8_t),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_21(
    Eurydice_slice serialized, Eurydice_slice ring_elements) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) /
               LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
        i0 * LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE +
            LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
        uint8_t);
    libcrux_ml_dsa_encoding_t0_deserialize_21(
        bytes, &Eurydice_slice_index(
                   ring_elements, i0,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    libcrux_ml_dsa_ntt_ntt_21(&Eurydice_slice_index(
        ring_elements, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of core.option.Option
with types libcrux_ml_dsa_polynomial_PolynomialRingElement
libcrux_ml_dsa_simd_avx2_vector_type_Vec256[5size_t]

*/
typedef struct Option_7e_s {
  Option_d8_tags tag;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b f0[5U];
} Option_7e;

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_x4
with const generics
- OUT_LEN= 576
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_x4_1b(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
  libcrux_sha3_avx2_x4_shake256(
      input0, input1, input2, input3,
      Eurydice_array_to_slice((size_t)576U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)576U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)576U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)576U, out3, uint8_t));
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake256x4)#2}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_x4_fb
with const generics
- OUT_LEN= 576
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_x4_fb_1b(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
  libcrux_ml_dsa_hash_functions_simd256_shake256_x4_1b(
      input0, input1, input2, input3, out0, out1, out2, out3);
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.gamma1.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_gamma1_deserialize_21(
    size_t gamma1_exponent, Eurydice_slice serialized,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)32U, result->simd_units, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_gamma1_deserialize_22(
        Eurydice_slice_subslice2(
            serialized, i0 * (gamma1_exponent + (size_t)1U),
            (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U), uint8_t),
        &result->simd_units[i0], gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_x4
with const generics
- OUT_LEN= 640
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_x4_c8(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
  libcrux_sha3_avx2_x4_shake256(
      input0, input1, input2, input3,
      Eurydice_array_to_slice((size_t)640U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)640U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)640U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)640U, out3, uint8_t));
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::simd256::Shake256x4)#2}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_x4_fb
with const generics
- OUT_LEN= 640
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_x4_fb_c8(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, uint8_t *out0, uint8_t *out1, uint8_t *out2,
    uint8_t *out3) {
  libcrux_ml_dsa_hash_functions_simd256_shake256_x4_c8(
      input0, input1, input2, input3, out0, out1, out2, out3);
}

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_hash_functions_simd256_shake256_1b(
    Eurydice_slice input, uint8_t *out) {
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)576U, out, uint8_t), input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_d9
with const generics
- OUTPUT_LENGTH= 576
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_d9_1b(Eurydice_slice input,
                                                     uint8_t *out) {
  libcrux_ml_dsa_hash_functions_simd256_shake256_1b(input, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_hash_functions_simd256_shake256_c8(
    Eurydice_slice input, uint8_t *out) {
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)640U, out, uint8_t), input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::simd256::Shake256)#1}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.simd256.shake256_d9
with const generics
- OUTPUT_LENGTH= 640
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_simd256_shake256_d9_c8(Eurydice_slice input,
                                                     uint8_t *out) {
  libcrux_ml_dsa_hash_functions_simd256_shake256_c8(input, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_mask_ring_element
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_sample_sample_mask_ring_element_18(
    uint8_t *seed, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result,
    size_t gamma1_exponent) {
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      uint8_t out[576U] = {0U};
      libcrux_ml_dsa_hash_functions_simd256_shake256_d9_1b(
          Eurydice_array_to_slice((size_t)66U, seed, uint8_t), out);
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out, uint8_t),
          result);
      break;
    }
    case 19U: {
      uint8_t out[640U] = {0U};
      libcrux_ml_dsa_hash_functions_simd256_shake256_d9_c8(
          Eurydice_array_to_slice((size_t)66U, seed, uint8_t), out);
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out, uint8_t),
          result);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_mask_vector
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_sample_sample_mask_vector_f4(
    size_t dimension, size_t gamma1_exponent, uint8_t *seed,
    uint16_t *domain_separator, Eurydice_slice mask) {
  uint8_t seed0[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t), domain_separator[0U],
      seed0);
  uint8_t seed1[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 1U, seed1);
  uint8_t seed2[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 2U, seed2);
  uint8_t seed3[66U];
  libcrux_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
      (uint32_t)domain_separator[0U] + 3U, seed3);
  domain_separator[0U] = (uint32_t)domain_separator[0U] + 4U;
  switch ((uint8_t)gamma1_exponent) {
    case 17U: {
      uint8_t out0[576U] = {0U};
      uint8_t out1[576U] = {0U};
      uint8_t out2[576U] = {0U};
      uint8_t out3[576U] = {0U};
      libcrux_ml_dsa_hash_functions_simd256_shake256_x4_fb_1b(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t), out0, out1,
          out2, out3);
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out0, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)0U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out1, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)1U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out2, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)2U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)576U, out3, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)3U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      break;
    }
    case 19U: {
      uint8_t out0[640U] = {0U};
      uint8_t out1[640U] = {0U};
      uint8_t out2[640U] = {0U};
      uint8_t out3[640U] = {0U};
      libcrux_ml_dsa_hash_functions_simd256_shake256_x4_fb_c8(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t), out0, out1,
          out2, out3);
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out0, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)0U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out1, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)1U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out2, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)2U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_encoding_gamma1_deserialize_21(
          gamma1_exponent, Eurydice_array_to_slice((size_t)640U, out3, uint8_t),
          &Eurydice_slice_index(
              mask, (size_t)3U,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  for (size_t i = (size_t)4U; i < dimension; i++) {
    size_t i0 = i;
    uint8_t seed4[66U];
    libcrux_ml_dsa_sample_add_error_domain_separator(
        Eurydice_array_to_slice((size_t)64U, seed, uint8_t),
        domain_separator[0U], seed4);
    domain_separator[0U] = (uint32_t)domain_separator[0U] + 1U;
    libcrux_ml_dsa_sample_sample_mask_ring_element_18(
        seed4,
        &Eurydice_slice_index(
            mask, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        gamma1_exponent);
  }
}

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_compute_matrix_x_mask_21(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice matrix,
    Eurydice_slice mask, Eurydice_slice result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b product =
          Eurydice_slice_index(
              mask, j, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
      libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
          &product, &Eurydice_slice_index(
                        matrix, i1 * columns_in_a + j,
                        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_polynomial_add_ff_21(
          &Eurydice_slice_index(
              result, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
          &product);
    }
    libcrux_ml_dsa_ntt_invert_ntt_montgomery_21(&Eurydice_slice_index(
        result, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.decompose_vector
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_arithmetic_decompose_vector_21(
    size_t dimension, int32_t gamma2, Eurydice_slice t, Eurydice_slice low,
    Eurydice_slice high) {
  for (size_t i0 = (size_t)0U; i0 < dimension; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)32U,
                     Eurydice_slice_index(
                         low, (size_t)0U,
                         libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                         libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
                         .simd_units,
                     __m256i),
                 __m256i);
         i++) {
      size_t j = i;
      libcrux_ml_dsa_simd_avx2_decompose_22(
          gamma2,
          &Eurydice_slice_index(
               t, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          &Eurydice_slice_index(
               low, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          &Eurydice_slice_index(
               high, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.commitment.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_commitment_serialize_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re,
    Eurydice_slice serialized) {
  size_t output_bytes_per_simd_unit =
      Eurydice_slice_len(serialized, uint8_t) / ((size_t)8U * (size_t)4U);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &re->simd_units[i0];
    libcrux_ml_dsa_simd_avx2_commitment_serialize_22(
        simd_unit,
        Eurydice_slice_subslice2(serialized, i0 * output_bytes_per_simd_unit,
                                 (i0 + (size_t)1U) * output_bytes_per_simd_unit,
                                 uint8_t));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.commitment.serialize_vector
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_commitment_serialize_vector_21(
    size_t ring_element_size, Eurydice_slice vector,
    Eurydice_slice serialized) {
  size_t offset = (size_t)0U;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t _cloop_j = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *ring_element =
        &Eurydice_slice_index(
            vector, _cloop_j,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
    libcrux_ml_dsa_encoding_commitment_serialize_21(
        ring_element,
        Eurydice_slice_subslice2(serialized, offset, offset + ring_element_size,
                                 uint8_t));
    offset = offset + ring_element_size;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_challenge_ring_element
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_hash_functions_simd256_Shake256 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_sample_sample_challenge_ring_element_18(
    Eurydice_slice seed, size_t number_of_ones,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re) {
  libcrux_sha3_portable_KeccakState state =
      libcrux_ml_dsa_hash_functions_simd256_init_absorb_final_d9(seed);
  uint8_t randomness0[136U];
  libcrux_ml_dsa_hash_functions_simd256_squeeze_first_block_d9(&state,
                                                               randomness0);
  uint8_t ret[8U];
  Result_15 dst;
  Eurydice_slice_to_array2(
      &dst,
      Eurydice_array_to_subslice2(randomness0, (size_t)0U, (size_t)8U, uint8_t),
      Eurydice_slice, uint8_t[8U]);
  unwrap_26_68(dst, ret);
  uint64_t signs = core_num__u64_9__from_le_bytes(ret);
  int32_t result[256U] = {0U};
  size_t out_index =
      Eurydice_slice_len(Eurydice_array_to_slice((size_t)256U, result, int32_t),
                         int32_t) -
      number_of_ones;
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)136U, randomness0, (size_t)8U, uint8_t, size_t);
  bool done = libcrux_ml_dsa_sample_inside_out_shuffle(uu____0, &out_index,
                                                       &signs, result);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[136U];
      libcrux_ml_dsa_hash_functions_simd256_squeeze_next_block_d9(&state,
                                                                  randomness);
      done = libcrux_ml_dsa_sample_inside_out_shuffle(
          Eurydice_array_to_slice((size_t)136U, randomness, uint8_t),
          &out_index, &signs, result);
    }
  }
  libcrux_ml_dsa_polynomial_from_i32_array_ff_21(
      Eurydice_array_to_slice((size_t)256U, result, int32_t), re);
}

/**
A monomorphic instance of libcrux_ml_dsa.matrix.vector_times_ring_element
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_vector_times_ring_element_21(
    Eurydice_slice vector,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *ring_element) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
        &Eurydice_slice_index(
            vector, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        ring_element);
    libcrux_ml_dsa_ntt_invert_ntt_montgomery_21(&Eurydice_slice_index(
        vector, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.matrix.add_vectors
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_add_vectors_21(
    size_t dimension, Eurydice_slice lhs, Eurydice_slice rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_polynomial_add_ff_21(
        &Eurydice_slice_index(
            lhs, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        &Eurydice_slice_index(
            rhs, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.subtract_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_polynomial_subtract_ff_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *self,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, self->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_subtract_22(&self->simd_units[i0],
                                         &rhs->simd_units[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.matrix.subtract_vectors
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_subtract_vectors_21(
    size_t dimension, Eurydice_slice lhs, Eurydice_slice rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_polynomial_subtract_ff_21(
        &Eurydice_slice_index(
            lhs, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        &Eurydice_slice_index(
            rhs, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.infinity_norm_exceeds_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_polynomial_infinity_norm_exceeds_ff_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *self, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, self->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_ml_dsa_simd_avx2_infinity_norm_exceeds_22(
          &self->simd_units[i0], bound);
    }
    result = uu____0;
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.vector_infinity_norm_exceeds
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_dsa_arithmetic_vector_infinity_norm_exceeds_21(Eurydice_slice vector,
                                                          int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               vector, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i++) {
    size_t _cloop_j = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *ring_element =
        &Eurydice_slice_index(
            vector, _cloop_j,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_ml_dsa_polynomial_infinity_norm_exceeds_ff_21(
          ring_element, bound);
    }
    result = uu____0;
  }
  return result;
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.to_i32_array_ff
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_polynomial_to_i32_array_ff_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *self,
    int32_t ret[256U]) {
  int32_t result[256U] = {0U};
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, self->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &self->simd_units[i0];
    __m256i *uu____0 = simd_unit;
    libcrux_ml_dsa_simd_avx2_to_coefficient_array_22(
        uu____0,
        Eurydice_array_to_subslice2(
            result, i0 * LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
            int32_t));
  }
  memcpy(ret, result, (size_t)256U * sizeof(int32_t));
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.make_hint
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_dsa_arithmetic_make_hint_21(Eurydice_slice low, Eurydice_slice high,
                                       int32_t gamma2, Eurydice_slice hint) {
  size_t true_hints = (size_t)0U;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b hint_simd =
      libcrux_ml_dsa_polynomial_zero_ff_21();
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                low, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(Eurydice_array_to_slice(
                                    (size_t)32U, hint_simd.simd_units, __m256i),
                                __m256i);
         i++) {
      size_t j = i;
      size_t one_hints_count = libcrux_ml_dsa_simd_avx2_compute_hint_22(
          &Eurydice_slice_index(
               low, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          &Eurydice_slice_index(
               high, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          gamma2, &hint_simd.simd_units[j]);
      true_hints = true_hints + one_hints_count;
    }
    int32_t uu____0[256U];
    libcrux_ml_dsa_polynomial_to_i32_array_ff_21(&hint_simd, uu____0);
    memcpy(Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U]),
           uu____0, (size_t)256U * sizeof(int32_t));
  }
  return true_hints;
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.gamma1.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_gamma1_serialize_21(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re,
    Eurydice_slice serialized, size_t gamma1_exponent) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    __m256i *simd_unit = &re->simd_units[i0];
    libcrux_ml_dsa_simd_avx2_gamma1_serialize_22(
        simd_unit,
        Eurydice_slice_subslice2(
            serialized, i0 * (gamma1_exponent + (size_t)1U),
            (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U), uint8_t),
        gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.signature.serialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_signature_serialize_21(
    Eurydice_slice commitment_hash, Eurydice_slice signer_response,
    Eurydice_slice hint, size_t commitment_hash_size, size_t columns_in_a,
    size_t rows_in_a, size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_slice signature) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice2(signature, offset, offset + commitment_hash_size,
                               uint8_t),
      commitment_hash, uint8_t);
  offset = offset + commitment_hash_size;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_encoding_gamma1_serialize_21(
        &Eurydice_slice_index(
            signer_response, i0,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        Eurydice_slice_subslice2(signature, offset,
                                 offset + gamma1_ring_element_size, uint8_t),
        gamma1_exponent);
    offset = offset + gamma1_ring_element_size;
  }
  size_t true_hints_seen = (size_t)0U;
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U;
         i <
         Eurydice_slice_len(Eurydice_array_to_slice(
                                (size_t)256U,
                                Eurydice_slice_index(hint, i1, int32_t[256U],
                                                     int32_t(*)[256U]),
                                int32_t),
                            int32_t);
         i++) {
      size_t j = i;
      if (Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U])[j] ==
          (int32_t)1) {
        Eurydice_slice_index(signature, offset + true_hints_seen, uint8_t,
                             uint8_t *) = (uint8_t)j;
        true_hints_seen++;
      }
    }
    Eurydice_slice_index(signature, offset + max_ones_in_hint + i1, uint8_t,
                         uint8_t *) = (uint8_t)true_hints_seen;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_internal
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_53
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_07(
    Eurydice_slice signing_key, Eurydice_slice message,
    Option_84 domain_separation_context, uint8_t randomness[32U],
    uint8_t *signature) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice remaining_serialized0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_signing = uu____1.fst;
  Eurydice_slice remaining_serialized1 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice verification_key_hash = uu____2.fst;
  Eurydice_slice remaining_serialized2 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s1_serialized = uu____3.fst;
  Eurydice_slice remaining_serialized = uu____3.snd;
  Eurydice_slice_uint8_t_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice s2_serialized = uu____4.fst;
  Eurydice_slice t0_serialized = uu____4.snd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b s1_as_ntt[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    s1_as_ntt[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b s2_as_ntt[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    s2_as_ntt[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b t0_as_ntt[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    t0_as_ntt[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s1_serialized,
      Eurydice_array_to_slice(
          (size_t)5U, s1_as_ntt,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s2_serialized,
      Eurydice_array_to_slice(
          (size_t)6U, s2_as_ntt,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_21(
      t0_serialized, Eurydice_array_to_slice(
                         (size_t)6U, t0_as_ntt,
                         libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b matrix[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    matrix[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_samplex4_avx2_matrix_flat_b8_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
      Eurydice_array_to_slice(
          (size_t)30U, matrix,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  uint8_t message_representative[64U] = {0U};
  libcrux_ml_dsa_ml_dsa_generic_derive_message_representative_7b(
      verification_key_hash, &domain_separation_context, message,
      message_representative);
  uint8_t mask_seed[64U] = {0U};
  libcrux_sha3_portable_incremental_Shake256Xof shake0 =
      libcrux_ml_dsa_hash_functions_portable_init_83();
  libcrux_ml_dsa_hash_functions_portable_absorb_83(&shake0, seed_for_signing);
  libcrux_ml_dsa_hash_functions_portable_absorb_83(
      &shake0, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
      &shake0,
      Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
  libcrux_ml_dsa_hash_functions_portable_squeeze_83(
      &shake0, Eurydice_array_to_slice((size_t)64U, mask_seed, uint8_t));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_67 commitment_hash0 = {.tag = None};
  Option_7e signer_response0 = {.tag = None};
  Option_f0 hint0 = {.tag = None};
  while (attempt < LIBCRUX_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b mask[5U];
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      mask[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
    }
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b w0[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      w0[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
    }
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b commitment[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      commitment[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
    }
    libcrux_ml_dsa_sample_sample_mask_vector_f4(
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT, mask_seed,
        &domain_separator_for_mask,
        Eurydice_array_to_slice(
            (size_t)5U, mask,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b a_x_mask[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      a_x_mask[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
    }
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b mask_ntt[5U];
    core_array___core__clone__Clone_for__Array_T__N___20__clone(
        (size_t)5U, mask, mask_ntt,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b, void *);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)5U, mask_ntt,
                     libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
                 libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
         i++) {
      size_t i0 = i;
      libcrux_ml_dsa_ntt_ntt_21(&mask_ntt[i0]);
    }
    libcrux_ml_dsa_matrix_compute_matrix_x_mask_21(
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)30U, matrix,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)5U, mask_ntt,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)6U, a_x_mask,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
    libcrux_ml_dsa_arithmetic_decompose_vector_21(
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
        Eurydice_array_to_slice(
            (size_t)6U, a_x_mask,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)6U, w0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)6U, commitment,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
    uint8_t commitment_hash_candidate[48U] = {0U};
    uint8_t commitment_serialized[768U] = {0U};
    libcrux_ml_dsa_encoding_commitment_serialize_vector_21(
        LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
        Eurydice_array_to_slice(
            (size_t)6U, commitment,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_sha3_portable_incremental_Shake256Xof shake =
        libcrux_ml_dsa_hash_functions_portable_init_83();
    libcrux_ml_dsa_hash_functions_portable_absorb_83(
        &shake,
        Eurydice_array_to_slice((size_t)64U, message_representative, uint8_t));
    libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
        &shake,
        Eurydice_array_to_slice((size_t)768U, commitment_serialized, uint8_t));
    libcrux_ml_dsa_hash_functions_portable_squeeze_83(
        &shake, Eurydice_array_to_slice((size_t)48U, commitment_hash_candidate,
                                        uint8_t));
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b verifier_challenge =
        libcrux_ml_dsa_polynomial_zero_ff_21();
    libcrux_ml_dsa_sample_sample_challenge_ring_element_18(
        Eurydice_array_to_slice((size_t)48U, commitment_hash_candidate,
                                uint8_t),
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_ml_dsa_ntt_ntt_21(&verifier_challenge);
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b challenge_times_s1[5U];
    core_array___core__clone__Clone_for__Array_T__N___20__clone(
        (size_t)5U, s1_as_ntt, challenge_times_s1,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b, void *);
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b challenge_times_s2[6U];
    core_array___core__clone__Clone_for__Array_T__N___20__clone(
        (size_t)6U, s2_as_ntt, challenge_times_s2,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b, void *);
    libcrux_ml_dsa_matrix_vector_times_ring_element_21(
        Eurydice_array_to_slice(
            (size_t)5U, challenge_times_s1,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        &verifier_challenge);
    libcrux_ml_dsa_matrix_vector_times_ring_element_21(
        Eurydice_array_to_slice(
            (size_t)6U, challenge_times_s2,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        &verifier_challenge);
    libcrux_ml_dsa_matrix_add_vectors_21(
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        Eurydice_array_to_slice(
            (size_t)5U, mask,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)5U, challenge_times_s1,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
    libcrux_ml_dsa_matrix_subtract_vectors_21(
        LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        Eurydice_array_to_slice(
            (size_t)6U, w0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
        Eurydice_array_to_slice(
            (size_t)6U, challenge_times_s2,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
    if (!libcrux_ml_dsa_arithmetic_vector_infinity_norm_exceeds_21(
            Eurydice_array_to_slice(
                (size_t)5U, mask,
                libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
            ((int32_t)1 << (uint32_t)
                 LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      if (!libcrux_ml_dsa_arithmetic_vector_infinity_norm_exceeds_21(
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
              LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 -
                  LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b
            challenge_times_t0[6U];
        core_array___core__clone__Clone_for__Array_T__N___20__clone(
            (size_t)6U, t0_as_ntt, challenge_times_t0,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b, void *);
        libcrux_ml_dsa_matrix_vector_times_ring_element_21(
            Eurydice_array_to_slice(
                (size_t)6U, challenge_times_t0,
                libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
            &verifier_challenge);
        if (!libcrux_ml_dsa_arithmetic_vector_infinity_norm_exceeds_21(
                Eurydice_array_to_slice(
                    (size_t)6U, challenge_times_t0,
                    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
                LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2)) {
          libcrux_ml_dsa_matrix_add_vectors_21(
              LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
              Eurydice_array_to_slice(
                  (size_t)6U, challenge_times_t0,
                  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
          int32_t hint_candidate[6U][256U] = {{0U}};
          size_t ones_in_hint = libcrux_ml_dsa_arithmetic_make_hint_21(
              Eurydice_array_to_slice(
                  (size_t)6U, w0,
                  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
              Eurydice_array_to_slice(
                  (size_t)6U, commitment,
                  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
              LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
              Eurydice_array_to_slice((size_t)6U, hint_candidate,
                                      int32_t[256U]));
          if (!(ones_in_hint >
                LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            /* Passing arrays by value in Rust generates a copy in C */
            uint8_t copy_of_commitment_hash_candidate[48U];
            memcpy(copy_of_commitment_hash_candidate, commitment_hash_candidate,
                   (size_t)48U * sizeof(uint8_t));
            Option_67 lit0;
            lit0.tag = Some;
            memcpy(lit0.f0, copy_of_commitment_hash_candidate,
                   (size_t)48U * sizeof(uint8_t));
            commitment_hash0 = lit0;
            /* Passing arrays by value in Rust generates a copy in C */
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b copy_of_mask[5U];
            memcpy(
                copy_of_mask, mask,
                (size_t)5U *
                    sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
            Option_7e lit1;
            lit1.tag = Some;
            memcpy(
                lit1.f0, copy_of_mask,
                (size_t)5U *
                    sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
            signer_response0 = lit1;
            /* Passing arrays by value in Rust generates a copy in C */
            int32_t copy_of_hint_candidate[6U][256U];
            memcpy(copy_of_hint_candidate, hint_candidate,
                   (size_t)6U * sizeof(int32_t[256U]));
            Option_f0 lit;
            lit.tag = Some;
            memcpy(lit.f0, copy_of_hint_candidate,
                   (size_t)6U * sizeof(int32_t[256U]));
            hint0 = lit;
          }
        }
      }
    }
  }
  Result_53 uu____8;
  if (commitment_hash0.tag == None) {
    uu____8 = (CLITERAL(Result_53){
        .tag = Err,
        .f0 = libcrux_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    uint8_t commitment_hash1[48U];
    memcpy(commitment_hash1, commitment_hash0.f0,
           (size_t)48U * sizeof(uint8_t));
    uint8_t commitment_hash[48U];
    memcpy(commitment_hash, commitment_hash1, (size_t)48U * sizeof(uint8_t));
    if (signer_response0.tag == None) {
      uu____8 = (CLITERAL(Result_53){
          .tag = Err,
          .f0 = libcrux_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b signer_response1[5U];
      memcpy(signer_response1, signer_response0.f0,
             (size_t)5U *
                 sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b signer_response[5U];
      memcpy(signer_response, signer_response1,
             (size_t)5U *
                 sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
      if (!(hint0.tag == None)) {
        int32_t hint1[6U][256U];
        memcpy(hint1, hint0.f0, (size_t)6U * sizeof(int32_t[256U]));
        int32_t hint[6U][256U];
        memcpy(hint, hint1, (size_t)6U * sizeof(int32_t[256U]));
        libcrux_ml_dsa_encoding_signature_serialize_21(
            Eurydice_array_to_slice((size_t)48U, commitment_hash, uint8_t),
            Eurydice_array_to_slice(
                (size_t)5U, signer_response,
                libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
            Eurydice_array_to_slice((size_t)6U, hint, int32_t[256U]),
            LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
            LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
            LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
            LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
            LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice((size_t)3309U, signature, uint8_t));
        return (CLITERAL(Result_53){.tag = Ok});
      }
      uu____8 = (CLITERAL(Result_53){
          .tag = Err,
          .f0 = libcrux_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____8;
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_53
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_07(Eurydice_slice signing_key,
                                                    Eurydice_slice message,
                                                    Eurydice_slice context,
                                                    uint8_t randomness[32U],
                                                    uint8_t *signature) {
  Result_a8 uu____0 = libcrux_ml_dsa_pre_hash_new_45(
      context, (CLITERAL(Option_30){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (CLITERAL(Result_53){
        .tag = Err,
        .f0 = libcrux_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
      dsc;
  Eurydice_slice uu____1 = signing_key;
  Eurydice_slice uu____2 = message;
  Option_84 uu____3 = {.tag = Some, .f0 = domain_separation_context};
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_07(
      uu____1, uu____2, uu____3, copy_of_randomness, signature);
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4 with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_2e
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_07(Eurydice_slice signing_key,
                                                Eurydice_slice message,
                                                Eurydice_slice context,
                                                uint8_t randomness[32U]) {
  libcrux_ml_dsa_types_MLDSASignature_8f signature =
      libcrux_ml_dsa_types_zero_8f_fa();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  Result_53 uu____4 = libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_07(
      uu____0, uu____1, uu____2, copy_of_randomness, signature.value);
  Result_2e uu____5;
  if (uu____4.tag == Ok) {
    uu____5 = (CLITERAL(Result_2e){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_ml_dsa_types_SigningError e = uu____4.f0;
    uu____5 = (CLITERAL(Result_2e){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____5;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign__inner(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_07(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Sign.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign__inner(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e libcrux_ml_dsa_ml_dsa_65_avx2_sign(
    libcrux_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_ml_dsa_types_as_ref_9b_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_53
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_mut__inner(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_07(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
 Sign.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_53
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_mut__inner(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_53 libcrux_ml_dsa_ml_dsa_65_avx2_sign_mut(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U], uint8_t *signature) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_mut(
      uu____0, uu____1, uu____2, copy_of_randomness, signature);
}

/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed_mut with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_portable_Shake128,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4,
libcrux_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_53
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_37(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U],
    uint8_t *signature) {
  if (!(Eurydice_slice_len(context, uint8_t) >
        LIBCRUX_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_ml_dsa_pre_hash_hash_3e_cc(message, pre_hash_buffer);
    Eurydice_slice uu____0 = context;
    Option_30 lit;
    lit.tag = Some;
    uint8_t ret[11U];
    libcrux_ml_dsa_pre_hash_oid_3e(ret);
    memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
    Result_a8 uu____1 = libcrux_ml_dsa_pre_hash_new_45(uu____0, lit);
    if (!(uu____1.tag == Ok)) {
      return (CLITERAL(Result_53){
          .tag = Err,
          .f0 = libcrux_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____1.val.case_Ok;
    libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
        dsc;
    Eurydice_slice uu____2 = signing_key;
    Eurydice_slice uu____3 = pre_hash_buffer;
    Option_84 uu____4 = {.tag = Some, .f0 = domain_separation_context};
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_randomness[32U];
    memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
    return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_07(
        uu____2, uu____3, uu____4, copy_of_randomness, signature);
  }
  return (CLITERAL(Result_53){
      .tag = Err, .f0 = libcrux_ml_dsa_types_SigningError_ContextTooLongError});
}

/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_portable_Shake128,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_simd256_Shake256x4,
libcrux_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_2e
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_37(
    Eurydice_slice signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  libcrux_ml_dsa_types_MLDSASignature_8f signature =
      libcrux_ml_dsa_types_zero_8f_fa();
  Eurydice_slice uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  Result_53 uu____5 =
      libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_37(
          uu____0, uu____1, uu____2, uu____3, copy_of_randomness,
          signature.value);
  Result_2e uu____6;
  if (uu____5.tag == Ok) {
    uu____6 = (CLITERAL(Result_2e){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_ml_dsa_types_SigningError e = uu____5.f0;
    uu____6 = (CLITERAL(Result_2e){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____6;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_pre_hashed_shake128__inner(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_slice((size_t)4032U, signing_key, uint8_t);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_37(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
 Sign (pre-hashed).
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_pre_hashed_shake128(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t randomness[32U]) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 = pre_hash_buffer;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_pre_hashed_shake128__inner(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_2e libcrux_ml_dsa_ml_dsa_65_avx2_sign_pre_hashed_shake128(
    libcrux_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t pre_hash_buffer[256U] = {0U};
  uint8_t *uu____0 = libcrux_ml_dsa_types_as_ref_9b_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  Eurydice_slice uu____3 =
      Eurydice_array_to_slice((size_t)256U, pre_hash_buffer, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_sign_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3, copy_of_randomness);
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.t1.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_dsa_encoding_t1_deserialize_21(
    Eurydice_slice serialized,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *result) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)32U, result->simd_units, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_t1_deserialize_22(
        Eurydice_slice_subslice2(
            serialized, i0 * LIBCRUX_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
            (i0 + (size_t)1U) * LIBCRUX_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
            uint8_t),
        &result->simd_units[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.verification_key.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_verification_key_deserialize_21(
    size_t rows_in_a, size_t verification_key_size, Eurydice_slice serialized,
    Eurydice_slice t1) {
  for (size_t i = (size_t)0U; i < rows_in_a; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_encoding_t1_deserialize_21(
        Eurydice_slice_subslice2(
            serialized, i0 * LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            (i0 + (size_t)1U) *
                LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
            uint8_t),
        &Eurydice_slice_index(
            t1, i0, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.signature.deserialize
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_encoding_signature_deserialize_21(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size, Eurydice_slice serialized,
    Eurydice_slice out_commitment_hash, Eurydice_slice out_signer_response,
    Eurydice_slice out_hint) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      serialized, commitment_hash_size, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice commitment_hash = uu____0.fst;
  Eurydice_slice rest_of_serialized = uu____0.snd;
  Eurydice_slice_copy(Eurydice_slice_subslice2(out_commitment_hash, (size_t)0U,
                                               commitment_hash_size, uint8_t),
                      commitment_hash, uint8_t);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      rest_of_serialized, gamma1_ring_element_size * columns_in_a, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice signer_response_serialized = uu____1.fst;
  Eurydice_slice hint_serialized = uu____1.snd;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_encoding_gamma1_deserialize_21(
        gamma1_exponent,
        Eurydice_slice_subslice2(
            signer_response_serialized, i0 * gamma1_ring_element_size,
            (i0 + (size_t)1U) * gamma1_ring_element_size, uint8_t),
        &Eurydice_slice_index(
            out_signer_response, i0,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
  size_t previous_true_hints_seen = (size_t)0U;
  core_ops_range_Range_08 iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          (CLITERAL(core_ops_range_Range_08){.start = (size_t)0U,
                                             .end = rows_in_a}),
          core_ops_range_Range_08, core_ops_range_Range_08);
  Result_41 uu____2;
  while (true) {
    Option_08 uu____3 =
        core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
            &iter, size_t, Option_08);
    if (uu____3.tag == None) {
      for (size_t i = previous_true_hints_seen; i < max_ones_in_hint; i++) {
        size_t j = i;
        if (!(Eurydice_slice_index(hint_serialized, j, uint8_t, uint8_t *) !=
              0U)) {
          continue;
        }
        uu____2 = (CLITERAL(Result_41){
            .tag = Err,
            .f0 = libcrux_ml_dsa_types_VerificationError_MalformedHintError});
        break;
      }
      return (CLITERAL(Result_41){.tag = Ok});
    } else {
      size_t i = uu____3.f0;
      size_t current_true_hints_seen = (size_t)Eurydice_slice_index(
          hint_serialized, max_ones_in_hint + i, uint8_t, uint8_t *);
      libcrux_ml_dsa_types_VerificationError uu____4;
      if (current_true_hints_seen < previous_true_hints_seen) {
        uu____4 = libcrux_ml_dsa_types_VerificationError_MalformedHintError;
        uu____2 = (CLITERAL(Result_41){.tag = Err, .f0 = uu____4});
      } else if (previous_true_hints_seen > max_ones_in_hint) {
        uu____4 = libcrux_ml_dsa_types_VerificationError_MalformedHintError;
        uu____2 = (CLITERAL(Result_41){.tag = Err, .f0 = uu____4});
      } else {
        for (size_t i0 = previous_true_hints_seen; i0 < current_true_hints_seen;
             i0++) {
          size_t j = i0;
          if (j > previous_true_hints_seen) {
            if (Eurydice_slice_index(hint_serialized, j, uint8_t, uint8_t *) <=
                Eurydice_slice_index(hint_serialized, j - (size_t)1U, uint8_t,
                                     uint8_t *)) {
              uu____2 = (CLITERAL(Result_41){
                  .tag = Err,
                  .f0 =
                      libcrux_ml_dsa_types_VerificationError_MalformedHintError});
            }
          }
          libcrux_ml_dsa_encoding_signature_set_hint(
              out_hint, i,
              (size_t)Eurydice_slice_index(hint_serialized, j, uint8_t,
                                           uint8_t *));
        }
        previous_true_hints_seen = current_true_hints_seen;
        continue;
      }
      break;
    }
  }
  return uu____2;
}

/**
A monomorphic instance of
libcrux_ml_dsa.simd.avx2.arithmetic.shift_left_then_reduce with const generics
- SHIFT_BY= 13
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_arithmetic_shift_left_then_reduce_84(
    __m256i *simd_unit) {
  __m256i shifted = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)13, simd_unit[0U], __m256i);
  __m256i quotient = libcrux_intrinsics_avx2_mm256_add_epi32(
      shifted, libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)1 << 22U));
  __m256i quotient0 =
      libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)23, quotient, __m256i);
  __m256i quotient_times_field_modulus =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(
          quotient0, libcrux_intrinsics_avx2_mm256_set1_epi32(
                         LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS));
  simd_unit[0U] = libcrux_intrinsics_avx2_mm256_sub_epi32(
      shifted, quotient_times_field_modulus);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
/**
A monomorphic instance of libcrux_ml_dsa.simd.avx2.shift_left_then_reduce_22
with const generics
- SHIFT_BY= 13
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_avx2_shift_left_then_reduce_22_84(__m256i *simd_unit) {
  libcrux_ml_dsa_simd_avx2_arithmetic_shift_left_then_reduce_84(simd_unit);
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics
- SHIFT_BY= 13
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_arithmetic_shift_left_then_reduce_3a(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)32U, re->simd_units, __m256i),
               __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_avx2_shift_left_then_reduce_22_84(&re->simd_units[i0]);
  }
}

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_ml_dsa.matrix.compute_w_approx
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_compute_w_approx_21(
    size_t rows_in_a, size_t columns_in_a, Eurydice_slice matrix,
    Eurydice_slice signer_response,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b
        *verifier_challenge_as_ntt,
    Eurydice_slice t1) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b inner_result =
        libcrux_ml_dsa_polynomial_zero_ff_21();
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b product =
          Eurydice_slice_index(
              matrix, i1 * columns_in_a + j,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *);
      libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
          &product, &Eurydice_slice_index(
                        signer_response, j,
                        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
      libcrux_ml_dsa_polynomial_add_ff_21(&inner_result, &product);
    }
    libcrux_ml_dsa_arithmetic_shift_left_then_reduce_3a(&Eurydice_slice_index(
        t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    libcrux_ml_dsa_ntt_ntt_21(&Eurydice_slice_index(
        t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    libcrux_ml_dsa_ntt_ntt_multiply_montgomery_21(
        &Eurydice_slice_index(
            t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *),
        verifier_challenge_as_ntt);
    libcrux_ml_dsa_polynomial_subtract_ff_21(
        &inner_result,
        &Eurydice_slice_index(
            t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
            libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
    Eurydice_slice_index(
        t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *) = inner_result;
    libcrux_ml_dsa_ntt_invert_ntt_montgomery_21(&Eurydice_slice_index(
        t1, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *));
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.use_hint
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_dsa_arithmetic_use_hint_21(
    int32_t gamma2, Eurydice_slice hint, Eurydice_slice re_vector) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                re_vector, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_4b tmp =
        libcrux_ml_dsa_polynomial_zero_ff_21();
    libcrux_ml_dsa_polynomial_from_i32_array_ff_21(
        Eurydice_array_to_slice(
            (size_t)256U,
            Eurydice_slice_index(hint, i1, int32_t[256U], int32_t(*)[256U]),
            int32_t),
        &tmp);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)32U,
                     Eurydice_slice_index(
                         re_vector, (size_t)0U,
                         libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
                         libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
                         .simd_units,
                     __m256i),
                 __m256i);
         i++) {
      size_t j = i;
      libcrux_ml_dsa_simd_avx2_use_hint_22(
          gamma2,
          &Eurydice_slice_index(
               re_vector, i1,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
               libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *)
               .simd_units[j],
          &tmp.simd_units[j]);
    }
    Eurydice_slice_index(
        re_vector, i1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b,
        libcrux_ml_dsa_polynomial_PolynomialRingElement_4b *) = tmp;
  }
}

/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_internal with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_07(
    uint8_t *verification_key, Eurydice_slice message,
    Option_84 domain_separation_context, uint8_t *signature_serialized) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t),
      LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice t1_serialized = uu____0.snd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b t1[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    t1[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  libcrux_ml_dsa_encoding_verification_key_deserialize_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE,
      t1_serialized,
      Eurydice_array_to_slice(
          (size_t)6U, t1, libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
  uint8_t deserialized_commitment_hash[48U] = {0U};
  libcrux_ml_dsa_polynomial_PolynomialRingElement_4b
      deserialized_signer_response[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    deserialized_signer_response[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
  }
  int32_t deserialized_hint[6U][256U] = {{0U}};
  Result_41 uu____1 = libcrux_ml_dsa_encoding_signature_deserialize_21(
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
      LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE,
      Eurydice_array_to_slice((size_t)3309U, signature_serialized, uint8_t),
      Eurydice_array_to_slice((size_t)48U, deserialized_commitment_hash,
                              uint8_t),
      Eurydice_array_to_slice(
          (size_t)5U, deserialized_signer_response,
          libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
      Eurydice_array_to_slice((size_t)6U, deserialized_hint, int32_t[256U]));
  Result_41 uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_ml_dsa_arithmetic_vector_infinity_norm_exceeds_21(
            Eurydice_array_to_slice(
                (size_t)5U, deserialized_signer_response,
                libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
            ((int32_t)2 << (uint32_t)
                 LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      uu____2 = (CLITERAL(Result_41){
          .tag = Err,
          .f0 =
              libcrux_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b matrix[30U];
      for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
        matrix[i] = libcrux_ml_dsa_polynomial_zero_ff_21();
      }
      libcrux_ml_dsa_samplex4_avx2_matrix_flat_b8_21(
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
          Eurydice_array_to_slice(
              (size_t)30U, matrix,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
      uint8_t verification_key_hash[64U] = {0U};
      libcrux_ml_dsa_hash_functions_simd256_shake256_d9_24(
          Eurydice_array_to_slice((size_t)1952U, verification_key, uint8_t),
          verification_key_hash);
      uint8_t message_representative[64U] = {0U};
      libcrux_ml_dsa_ml_dsa_generic_derive_message_representative_7b(
          Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
          &domain_separation_context, message, message_representative);
      libcrux_ml_dsa_polynomial_PolynomialRingElement_4b verifier_challenge =
          libcrux_ml_dsa_polynomial_zero_ff_21();
      libcrux_ml_dsa_sample_sample_challenge_ring_element_18(
          Eurydice_array_to_slice((size_t)48U, deserialized_commitment_hash,
                                  uint8_t),
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_ml_dsa_ntt_ntt_21(&verifier_challenge);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)5U, deserialized_signer_response,
                       libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_4b);
           i++) {
        size_t i0 = i;
        libcrux_ml_dsa_ntt_ntt_21(&deserialized_signer_response[i0]);
      }
      libcrux_ml_dsa_matrix_compute_w_approx_21(
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
          Eurydice_array_to_slice(
              (size_t)30U, matrix,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
          Eurydice_array_to_slice(
              (size_t)5U, deserialized_signer_response,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
          &verifier_challenge,
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
      uint8_t recomputed_commitment_hash[48U] = {0U};
      libcrux_ml_dsa_arithmetic_use_hint_21(
          LIBCRUX_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
          Eurydice_array_to_slice((size_t)6U, deserialized_hint, int32_t[256U]),
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b));
      uint8_t commitment_serialized[768U] = {0U};
      libcrux_ml_dsa_encoding_commitment_serialize_vector_21(
          LIBCRUX_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
          Eurydice_array_to_slice(
              (size_t)6U, t1,
              libcrux_ml_dsa_polynomial_PolynomialRingElement_4b),
          Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                  uint8_t));
      libcrux_sha3_portable_incremental_Shake256Xof shake =
          libcrux_ml_dsa_hash_functions_portable_init_83();
      libcrux_ml_dsa_hash_functions_portable_absorb_83(
          &shake, Eurydice_array_to_slice((size_t)64U, message_representative,
                                          uint8_t));
      libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
          &shake, Eurydice_array_to_slice((size_t)768U, commitment_serialized,
                                          uint8_t));
      libcrux_ml_dsa_hash_functions_portable_squeeze_83(
          &shake, Eurydice_array_to_slice((size_t)48U,
                                          recomputed_commitment_hash, uint8_t));
      if (core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
              (size_t)48U, deserialized_commitment_hash,
              recomputed_commitment_hash, uint8_t, uint8_t, bool)) {
        uu____2 = (CLITERAL(Result_41){.tag = Ok});
      } else {
        uu____2 = (CLITERAL(Result_41){
            .tag = Err,
            .f0 =
                libcrux_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (CLITERAL(Result_41){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_07(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  Result_a8 uu____0 = libcrux_ml_dsa_pre_hash_new_45(
      context, (CLITERAL(Option_30){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (CLITERAL(Result_41){
        .tag = Err,
        .f0 =
            libcrux_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
      dsc;
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_07(
      verification_key_serialized, message,
      (CLITERAL(Option_84){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify__inner(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_07(
      verification_key, message, context, signature);
}

/**
 Verify.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify__inner(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41 libcrux_ml_dsa_ml_dsa_65_avx2_verify(
    libcrux_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_ml_dsa_types_MLDSASignature_8f *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify(
      libcrux_ml_dsa_types_as_ref_66_97(verification_key), message, context,
      libcrux_ml_dsa_types_as_ref_8f_fa(signature));
}

/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_pre_hashed with types
libcrux_ml_dsa_simd_avx2_vector_type_Vec256,
libcrux_ml_dsa_samplex4_avx2_AVX2Sampler,
libcrux_ml_dsa_hash_functions_portable_Shake128,
libcrux_ml_dsa_hash_functions_simd256_Shake128x4,
libcrux_ml_dsa_hash_functions_simd256_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_37(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, Eurydice_slice pre_hash_buffer,
    uint8_t *signature_serialized) {
  libcrux_ml_dsa_pre_hash_hash_3e_cc(message, pre_hash_buffer);
  Eurydice_slice uu____0 = context;
  Option_30 lit;
  lit.tag = Some;
  uint8_t ret[11U];
  libcrux_ml_dsa_pre_hash_oid_3e(ret);
  memcpy(lit.f0, ret, (size_t)11U * sizeof(uint8_t));
  Result_a8 uu____1 = libcrux_ml_dsa_pre_hash_new_45(uu____0, lit);
  if (!(uu____1.tag == Ok)) {
    return (CLITERAL(Result_41){
        .tag = Err,
        .f0 =
            libcrux_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____1.val.case_Ok;
  libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
      dsc;
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_07(
      verification_key_serialized, pre_hash_buffer,
      (CLITERAL(Option_84){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify_pre_hashed_shake128__inner(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_37(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify_pre_hashed_shake128(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    Eurydice_slice pre_hash_buffer, uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify_pre_hashed_shake128__inner(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Result_41
libcrux_ml_dsa_ml_dsa_65_avx2_verify_pre_hashed_shake128(
    libcrux_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_ml_dsa_types_MLDSASignature_8f *signature) {
  uint8_t pre_hash_buffer[256U] = {0U};
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_avx2_ml_dsa_65_verify_pre_hashed_shake128(
      libcrux_ml_dsa_types_as_ref_66_97(verification_key), message, context,
      Eurydice_array_to_slice((size_t)256U, pre_hash_buffer, uint8_t),
      libcrux_ml_dsa_types_as_ref_8f_fa(signature));
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_is_bit_set(
    size_t number, uint8_t bit_position) {
  return (number & (size_t)1U << (uint32_t)bit_position) >>
             (uint32_t)bit_position ==
         (size_t)1U;
}

KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_generate_shuffle_table(
    uint8_t ret[16U][16U]) {
  uint8_t byte_shuffles[16U][16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    uint8_t repeat_expression[16U];
    memset(repeat_expression, 255U, (size_t)16U * sizeof(uint8_t));
    memcpy(byte_shuffles[i], repeat_expression, (size_t)16U * sizeof(uint8_t));
  }
  for (size_t i0 = (size_t)0U; i0 < (size_t)1U << 4U; i0++) {
    size_t bit_pattern = i0;
    size_t byte_shuffles_index = (size_t)0U;
    for (uint8_t i = 0U; i < 4U; i = (uint32_t)i + 1U) {
      uint8_t bit_position = i;
      if (libcrux_ml_dsa_simd_avx2_rejection_sample_shuffle_table_is_bit_set(
              bit_pattern, bit_position)) {
        byte_shuffles[bit_pattern][byte_shuffles_index] =
            (uint32_t)bit_position * 4U;
        byte_shuffles_index++;
        byte_shuffles[bit_pattern][byte_shuffles_index] =
            (uint32_t)bit_position * 4U + 1U;
        byte_shuffles_index++;
        byte_shuffles[bit_pattern][byte_shuffles_index] =
            (uint32_t)bit_position * 4U + 2U;
        byte_shuffles_index++;
        byte_shuffles[bit_pattern][byte_shuffles_index] =
            (uint32_t)bit_position * 4U + 3U;
        byte_shuffles_index++;
      }
    }
  }
  memcpy(ret, byte_shuffles, (size_t)16U * sizeof(uint8_t[16U]));
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_dsa::simd::avx2::vector_type::Vec256)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_ml_dsa_simd_avx2_vector_type_clone_b1(
    __m256i *self) {
  return self[0U];
}

typedef __m256i libcrux_ml_dsa_simd_avx2_vector_type_AVX2RingElement[32U];

#if defined(__cplusplus)
}
#endif

#define __libcrux_mldsa65_avx2_H_DEFINED
#endif
