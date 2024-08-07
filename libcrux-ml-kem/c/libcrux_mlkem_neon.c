/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: f4283998bcc3c86677cf0e03a6fa71913a524658
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: 878f09c21a4312320518388a0d902986b08e030a
 */

#include "internal/libcrux_mlkem_neon.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input,
                                                          uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_neon_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input,
                                                          uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_neon_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t, Eurydice_slice),
      input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_ZERO(void) {
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)0),
      .high = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)0)});
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ZERO_20(void) {
  return libcrux_ml_kem_vector_neon_vector_type_ZERO();
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_i16_array(Eurydice_slice array) {
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low =
          libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_slice_subslice2(
              array, (size_t)0U, (size_t)8U, int16_t, Eurydice_slice)),
      .high =
          libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_slice_subslice2(
              array, (size_t)8U, (size_t)16U, int16_t, Eurydice_slice))});
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_i16_array_20(Eurydice_slice array) {
  return libcrux_ml_kem_vector_neon_vector_type_from_i16_array(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_vector_type_to_i16_array(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t ret[16U]) {
  int16_t out[16U] = {0U};
  libcrux_intrinsics_arm64_extract__vst1q_s16(
      Eurydice_array_to_subslice2(out, (size_t)0U, (size_t)8U, int16_t,
                                  Eurydice_slice),
      v.low);
  libcrux_intrinsics_arm64_extract__vst1q_s16(
      Eurydice_array_to_subslice2(out, (size_t)8U, (size_t)16U, int16_t,
                                  Eurydice_slice),
      v.high);
  memcpy(ret, out, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_to_i16_array_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x, int16_t ret[16U]) {
  libcrux_ml_kem_vector_neon_vector_type_to_i16_array(x, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_add(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  lhs.low = libcrux_intrinsics_arm64_extract__vaddq_s16(lhs.low, rhs->low);
  lhs.high = libcrux_intrinsics_arm64_extract__vaddq_s16(lhs.high, rhs->high);
  return lhs;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_add_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  return libcrux_ml_kem_vector_neon_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_sub(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  lhs.low = libcrux_intrinsics_arm64_extract__vsubq_s16(lhs.low, rhs->low);
  lhs.high = libcrux_intrinsics_arm64_extract__vsubq_s16(lhs.high, rhs->high);
  return lhs;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_sub_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  return libcrux_ml_kem_vector_neon_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  v.low = libcrux_intrinsics_arm64_extract__vmulq_n_s16(v.low, c);
  v.high = libcrux_intrinsics_arm64_extract__vmulq_n_s16(v.high, c);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_multiply_by_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  return libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(v, c);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  uint8_t c0 = libcrux_intrinsics_arm64_extract__vdupq_n_s16(c);
  v.low = libcrux_intrinsics_arm64_extract__vandq_s16(v.low, c0);
  v.high = libcrux_intrinsics_arm64_extract__vandq_s16(v.high, c0);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_bitwise_and_with_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  return libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(v, c);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t c = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)3329);
  uint8_t m0 = libcrux_intrinsics_arm64_extract__vcgeq_s16(v.low, c);
  uint8_t m1 = libcrux_intrinsics_arm64_extract__vcgeq_s16(v.high, c);
  uint8_t c0 = libcrux_intrinsics_arm64_extract__vandq_s16(
      c, libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(m0));
  uint8_t c1 = libcrux_intrinsics_arm64_extract__vandq_s16(
      c, libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(m1));
  v.low = libcrux_intrinsics_arm64_extract__vsubq_s16(v.low, c0);
  v.high = libcrux_intrinsics_arm64_extract__vsubq_s16(v.high, c1);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_cond_subtract_3329_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(v);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(uint8_t v) {
  uint8_t adder = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)1024);
  uint8_t vec = libcrux_intrinsics_arm64_extract__vqdmulhq_n_s16(
      v, LIBCRUX_ML_KEM_VECTOR_NEON_ARITHMETIC_BARRETT_MULTIPLIER);
  uint8_t vec0 = libcrux_intrinsics_arm64_extract__vaddq_s16(vec, adder);
  uint8_t quotient =
      libcrux_intrinsics_arm64_extract__vshrq_n_s16((int32_t)11, vec0, uint8_t);
  uint8_t sub = libcrux_intrinsics_arm64_extract__vmulq_n_s16(
      quotient, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_intrinsics_arm64_extract__vsubq_s16(v, sub);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  v.low = libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(v.low);
  v.high =
      libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(v.high);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_barrett_reduce_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce(v);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
    uint8_t low, uint8_t high) {
  uint8_t k = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
      libcrux_intrinsics_arm64_extract__vmulq_n_u16(
          libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(low),
          (uint16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  uint8_t c = libcrux_intrinsics_arm64_extract__vshrq_n_s16(
      (int32_t)1,
      libcrux_intrinsics_arm64_extract__vqdmulhq_n_s16(
          k, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS),
      uint8_t);
  return libcrux_intrinsics_arm64_extract__vsubq_s16(high, c);
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
    uint8_t v, int16_t c) {
  uint8_t v_low = libcrux_intrinsics_arm64_extract__vmulq_n_s16(v, c);
  uint8_t v_high = libcrux_intrinsics_arm64_extract__vshrq_n_s16(
      (int32_t)1, libcrux_intrinsics_arm64_extract__vqdmulhq_n_s16(v, c),
      uint8_t);
  return libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
      v_low, v_high);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  v.low =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
          v.low, c);
  v.high =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
          v.high, c);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  return libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant(
      v, c);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_compress_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t half = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)1664);
  uint8_t quarter = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)832);
  uint8_t shifted = libcrux_intrinsics_arm64_extract__vsubq_s16(half, v.low);
  uint8_t mask0 = libcrux_intrinsics_arm64_extract__vshrq_n_s16(
      (int32_t)15, shifted, uint8_t);
  uint8_t shifted_to_positive =
      libcrux_intrinsics_arm64_extract__veorq_s16(mask0, shifted);
  uint8_t shifted_positive_in_range =
      libcrux_intrinsics_arm64_extract__vsubq_s16(shifted_to_positive, quarter);
  v.low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
      libcrux_intrinsics_arm64_extract__vshrq_n_u16(
          (int32_t)15,
          libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(
              shifted_positive_in_range),
          uint8_t));
  uint8_t shifted0 = libcrux_intrinsics_arm64_extract__vsubq_s16(half, v.high);
  uint8_t mask = libcrux_intrinsics_arm64_extract__vshrq_n_s16(
      (int32_t)15, shifted0, uint8_t);
  uint8_t shifted_to_positive0 =
      libcrux_intrinsics_arm64_extract__veorq_s16(mask, shifted0);
  uint8_t shifted_positive_in_range0 =
      libcrux_intrinsics_arm64_extract__vsubq_s16(shifted_to_positive0,
                                                  quarter);
  v.high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
      libcrux_intrinsics_arm64_extract__vshrq_n_u16(
          (int32_t)15,
          libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(
              shifted_positive_in_range0),
          uint8_t));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_1_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_compress_compress_1(v);
}

KRML_MUSTINLINE int16_t
libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
    int16_t coefficient_bits) {
  int16_t uu____0;
  switch (coefficient_bits) {
    case 4: {
      uu____0 = (int16_t)15;
      break;
    }
    case 5: {
      uu____0 = (int16_t)31;
      break;
    }
    case 10: {
      uu____0 = (int16_t)1023;
      break;
    }
    case 11: {
      uu____0 = (int16_t)2047;
      break;
    }
    default: {
      int16_t x = coefficient_bits;
      uu____0 = ((int16_t)1 << (uint32_t)x) - (int16_t)1;
    }
  }
  return uu____0;
}

KRML_MUSTINLINE uint8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(uint8_t v,
                                                                    uint8_t c) {
  uint8_t v_low = libcrux_intrinsics_arm64_extract__vmulq_s16(v, c);
  uint8_t v_high = libcrux_intrinsics_arm64_extract__vshrq_n_s16(
      (int32_t)1, libcrux_intrinsics_arm64_extract__vqdmulhq_s16(v, c),
      uint8_t);
  return libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
      v_low, v_high);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  int16_t zetas[8U] = {zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4};
  uint8_t zeta = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, zetas, int16_t, Eurydice_slice));
  uint8_t dup_a = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.high)));
  uint8_t dup_b = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.high)));
  uint8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(dup_b,
                                                                          zeta);
  uint8_t b = libcrux_intrinsics_arm64_extract__vsubq_s16(dup_a, t);
  uint8_t a = libcrux_intrinsics_arm64_extract__vaddq_s16(dup_a, t);
  v.low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(b)));
  v.high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(b)));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_1_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(a, zeta1, zeta2, zeta3,
                                                         zeta4);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2) {
  int16_t zetas[8U] = {zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2};
  uint8_t zeta = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, zetas, int16_t, Eurydice_slice));
  uint8_t dup_a = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn1q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.high)));
  uint8_t dup_b = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn2q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.high)));
  uint8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(dup_b,
                                                                          zeta);
  uint8_t b = libcrux_intrinsics_arm64_extract__vsubq_s16(dup_a, t);
  uint8_t a = libcrux_intrinsics_arm64_extract__vaddq_s16(dup_a, t);
  v.low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn1q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(b)));
  v.high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn2q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(b)));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_2_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(a, zeta1, zeta2);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta) {
  uint8_t zeta0 = libcrux_intrinsics_arm64_extract__vdupq_n_s16(zeta);
  uint8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          v.high, zeta0);
  v.high = libcrux_intrinsics_arm64_extract__vsubq_s16(v.low, t);
  v.low = libcrux_intrinsics_arm64_extract__vaddq_s16(v.low, t);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_3_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  int16_t zetas[8U] = {zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4};
  uint8_t zeta = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, zetas, int16_t, Eurydice_slice));
  uint8_t a0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.high)));
  uint8_t b0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(v.high)));
  uint8_t b_minus_a = libcrux_intrinsics_arm64_extract__vsubq_s16(b0, a0);
  uint8_t a = libcrux_intrinsics_arm64_extract__vaddq_s16(a0, b0);
  uint8_t a1 =
      libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(a);
  uint8_t b =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          b_minus_a, zeta);
  v.low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(a1),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(b)));
  v.high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(a1),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(b)));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(a, zeta1, zeta2,
                                                             zeta3, zeta4);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2) {
  int16_t zetas[8U] = {zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2};
  uint8_t zeta = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, zetas, int16_t, Eurydice_slice));
  uint8_t a0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn1q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.high)));
  uint8_t b0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn2q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.low),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(v.high)));
  uint8_t b_minus_a = libcrux_intrinsics_arm64_extract__vsubq_s16(b0, a0);
  uint8_t a = libcrux_intrinsics_arm64_extract__vaddq_s16(a0, b0);
  uint8_t b =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          b_minus_a, zeta);
  v.low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn1q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(b)));
  v.high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
      libcrux_intrinsics_arm64_extract__vtrn2q_s64(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(a),
          libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(b)));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(a, zeta1, zeta2);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta) {
  uint8_t zeta0 = libcrux_intrinsics_arm64_extract__vdupq_n_s16(zeta);
  uint8_t b_minus_a =
      libcrux_intrinsics_arm64_extract__vsubq_s16(v.high, v.low);
  v.low = libcrux_intrinsics_arm64_extract__vaddq_s16(v.low, v.high);
  v.high = libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
      b_minus_a, zeta0);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_multiply(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  int16_t zetas[8U] = {zeta1, zeta3, -zeta1, -zeta3,
                       zeta2, zeta4, -zeta2, -zeta4};
  uint8_t zeta = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, zetas, int16_t, Eurydice_slice));
  uint8_t a0 =
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(lhs->low, lhs->high);
  uint8_t a1 =
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(lhs->low, lhs->high);
  uint8_t b0 =
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(rhs->low, rhs->high);
  uint8_t b1 =
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(rhs->low, rhs->high);
  uint8_t a1b1 =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(a1,
                                                                          b1);
  uint8_t a1b1_low = libcrux_intrinsics_arm64_extract__vmull_s16(
      libcrux_intrinsics_arm64_extract__vget_low_s16(a1b1),
      libcrux_intrinsics_arm64_extract__vget_low_s16(zeta));
  uint8_t a1b1_high =
      libcrux_intrinsics_arm64_extract__vmull_high_s16(a1b1, zeta);
  uint8_t fst_low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vmlal_s16(
          a1b1_low, libcrux_intrinsics_arm64_extract__vget_low_s16(a0),
          libcrux_intrinsics_arm64_extract__vget_low_s16(b0)));
  uint8_t fst_high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vmlal_high_s16(a1b1_high, a0, b0));
  uint8_t a0b1_low = libcrux_intrinsics_arm64_extract__vmull_s16(
      libcrux_intrinsics_arm64_extract__vget_low_s16(a0),
      libcrux_intrinsics_arm64_extract__vget_low_s16(b1));
  uint8_t a0b1_high = libcrux_intrinsics_arm64_extract__vmull_high_s16(a0, b1);
  uint8_t snd_low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vmlal_s16(
          a0b1_low, libcrux_intrinsics_arm64_extract__vget_low_s16(a1),
          libcrux_intrinsics_arm64_extract__vget_low_s16(b0)));
  uint8_t snd_high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vmlal_high_s16(a0b1_high, a1, b0));
  uint8_t fst_low16 =
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(fst_low, fst_high);
  uint8_t fst_high16 =
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(fst_low, fst_high);
  uint8_t snd_low16 =
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(snd_low, snd_high);
  uint8_t snd_high16 =
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(snd_low, snd_high);
  uint8_t fst =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
          fst_low16, fst_high16);
  uint8_t snd =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
          snd_low16, snd_high16);
  uint8_t low0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(fst, snd));
  uint8_t high0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(fst, snd));
  uint8_t low1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(low0, high0));
  uint8_t high1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(low0, high0));
  uint8_t indexes[16U] = {0U, 1U, 2U, 3U, 8U,  9U,  10U, 11U,
                          4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U};
  uint8_t index = libcrux_intrinsics_arm64_extract__vld1q_u8(
      Eurydice_array_to_slice((size_t)16U, indexes, uint8_t, Eurydice_slice));
  uint8_t low2 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u8(
      libcrux_intrinsics_arm64_extract__vqtbl1q_u8(
          libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s16(low1), index));
  uint8_t high2 = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u8(
      libcrux_intrinsics_arm64_extract__vqtbl1q_u8(
          libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s16(high1),
          index));
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = low2, .high = high2});
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_multiply_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_multiply(lhs, rhs, zeta1, zeta2,
                                                     zeta3, zeta4);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[2U]) {
  int16_t shifter[8U] = {(int16_t)0, (int16_t)1, (int16_t)2, (int16_t)3,
                         (int16_t)4, (int16_t)5, (int16_t)6, (int16_t)7};
  uint8_t shift = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, shifter, int16_t, Eurydice_slice));
  uint8_t low0 = libcrux_intrinsics_arm64_extract__vshlq_s16(v.low, shift);
  uint8_t high0 = libcrux_intrinsics_arm64_extract__vshlq_s16(v.high, shift);
  int16_t low = libcrux_intrinsics_arm64_extract__vaddvq_s16(low0);
  int16_t high = libcrux_intrinsics_arm64_extract__vaddvq_s16(high0);
  ret[0U] = (uint8_t)low;
  ret[1U] = (uint8_t)high;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_1_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[2U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_1(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_1(Eurydice_slice a) {
  uint8_t one = libcrux_intrinsics_arm64_extract__vdupq_n_s16((int16_t)1);
  uint8_t low0 = libcrux_intrinsics_arm64_extract__vdupq_n_s16((
      int16_t)Eurydice_slice_index(a, (size_t)0U, uint8_t, uint8_t *, uint8_t));
  uint8_t high0 = libcrux_intrinsics_arm64_extract__vdupq_n_s16((
      int16_t)Eurydice_slice_index(a, (size_t)1U, uint8_t, uint8_t *, uint8_t));
  int16_t shifter[8U] = {(int16_t)0,  (int16_t)255, (int16_t)-2, (int16_t)-3,
                         (int16_t)-4, (int16_t)-5,  (int16_t)-6, (int16_t)-7};
  uint8_t shift = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, shifter, int16_t, Eurydice_slice));
  uint8_t low = libcrux_intrinsics_arm64_extract__vshlq_s16(low0, shift);
  uint8_t high = libcrux_intrinsics_arm64_extract__vshlq_s16(high0, shift);
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = libcrux_intrinsics_arm64_extract__vandq_s16(low, one),
      .high = libcrux_intrinsics_arm64_extract__vandq_s16(high, one)});
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_1_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_1(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[8U]) {
  int16_t shifter[8U] = {(int16_t)0, (int16_t)4, (int16_t)8, (int16_t)12,
                         (int16_t)0, (int16_t)4, (int16_t)8, (int16_t)12};
  uint8_t shift = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, shifter, int16_t, Eurydice_slice));
  uint8_t lowt = libcrux_intrinsics_arm64_extract__vshlq_u16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(v.low), shift);
  uint8_t hight = libcrux_intrinsics_arm64_extract__vshlq_u16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(v.high), shift);
  uint64_t sum0 = (uint64_t)libcrux_intrinsics_arm64_extract__vaddv_u16(
      libcrux_intrinsics_arm64_extract__vget_low_u16(lowt));
  uint64_t sum1 = (uint64_t)libcrux_intrinsics_arm64_extract__vaddv_u16(
      libcrux_intrinsics_arm64_extract__vget_high_u16(lowt));
  uint64_t sum2 = (uint64_t)libcrux_intrinsics_arm64_extract__vaddv_u16(
      libcrux_intrinsics_arm64_extract__vget_low_u16(hight));
  uint64_t sum3 = (uint64_t)libcrux_intrinsics_arm64_extract__vaddv_u16(
      libcrux_intrinsics_arm64_extract__vget_high_u16(hight));
  uint64_t sum = ((sum0 | sum1 << 16U) | sum2 << 32U) | sum3 << 48U;
  uint8_t ret0[8U];
  core_num__u64_9__to_le_bytes(sum, ret0);
  memcpy(ret, ret0, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_4_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[8U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_4(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_4(Eurydice_slice v) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector input =
      libcrux_ml_kem_vector_portable_deserialize_4_0d(v);
  int16_t input_i16s[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(input, input_i16s);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lit;
  lit.low =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          input_i16s, (size_t)0U, (size_t)8U, int16_t, Eurydice_slice));
  lit.high =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          input_i16s, (size_t)8U, (size_t)16U, int16_t, Eurydice_slice));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_4_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_4(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[10U]) {
  int16_t out_i16s[16U];
  libcrux_ml_kem_vector_neon_vector_type_to_i16_array(v, out_i16s);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector out =
      libcrux_ml_kem_vector_portable_from_i16_array_0d(Eurydice_array_to_slice(
          (size_t)16U, out_i16s, int16_t, Eurydice_slice));
  uint8_t ret0[10U];
  libcrux_ml_kem_vector_portable_serialize_5_0d(out, ret0);
  memcpy(ret, ret0, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_5_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[10U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_5(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_5(Eurydice_slice v) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_5_0d(v);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lit;
  lit.low =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)0U, (size_t)8U, int16_t, Eurydice_slice));
  lit.high =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)8U, (size_t)16U, int16_t, Eurydice_slice));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_5_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_5(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_10(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[20U]) {
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(v.low, v.low));
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(v.low, v.low));
  uint8_t mixt = libcrux_intrinsics_arm64_extract__vsliq_n_s32(
      (int32_t)10, low00, low10, uint8_t);
  uint8_t low0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(mixt, mixt));
  uint8_t low1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(mixt, mixt));
  uint8_t low_mix = libcrux_intrinsics_arm64_extract__vsliq_n_s64(
      (int32_t)20, low0, low1, uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(v.high, v.high));
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(v.high, v.high));
  uint8_t mixt0 = libcrux_intrinsics_arm64_extract__vsliq_n_s32(
      (int32_t)10, high00, high10, uint8_t);
  uint8_t high0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(mixt0, mixt0));
  uint8_t high1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(mixt0, mixt0));
  uint8_t high_mix = libcrux_intrinsics_arm64_extract__vsliq_n_s64(
      (int32_t)20, high0, high1, uint8_t);
  uint8_t result32[32U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      result32, (size_t)0U, (size_t)16U, uint8_t, Eurydice_slice);
  libcrux_intrinsics_arm64_extract__vst1q_u8(
      uu____0, libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s64(low_mix));
  Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
      result32, (size_t)16U, (size_t)32U, uint8_t, Eurydice_slice);
  libcrux_intrinsics_arm64_extract__vst1q_u8(
      uu____1,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s64(high_mix));
  uint8_t result[20U] = {0U};
  Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
      result, (size_t)0U, (size_t)5U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_array_to_subslice2(result32, (size_t)0U, (size_t)5U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
      result, (size_t)5U, (size_t)10U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_array_to_subslice2(result32, (size_t)8U, (size_t)13U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice2(
      result, (size_t)10U, (size_t)15U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4,
      Eurydice_array_to_subslice2(result32, (size_t)16U, (size_t)21U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____5 = Eurydice_array_to_subslice2(
      result, (size_t)15U, (size_t)20U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____5,
      Eurydice_array_to_subslice2(result32, (size_t)24U, (size_t)29U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  memcpy(ret, result, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_10_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[20U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_10(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_10(Eurydice_slice v) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_10_0d(v);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lit;
  lit.low =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)0U, (size_t)8U, int16_t, Eurydice_slice));
  lit.high =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)8U, (size_t)16U, int16_t, Eurydice_slice));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_10_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_10(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_11(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[22U]) {
  int16_t out_i16s[16U];
  libcrux_ml_kem_vector_neon_vector_type_to_i16_array(v, out_i16s);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector out =
      libcrux_ml_kem_vector_portable_from_i16_array_0d(Eurydice_array_to_slice(
          (size_t)16U, out_i16s, int16_t, Eurydice_slice));
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_11_0d(out, ret0);
  memcpy(ret, ret0, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_11_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[22U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_11(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_11(Eurydice_slice v) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector output =
      libcrux_ml_kem_vector_portable_deserialize_11_0d(v);
  int16_t array[16U];
  libcrux_ml_kem_vector_portable_to_i16_array_0d(output, array);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lit;
  lit.low =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)0U, (size_t)8U, int16_t, Eurydice_slice));
  lit.high =
      libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_array_to_subslice2(
          array, (size_t)8U, (size_t)16U, int16_t, Eurydice_slice));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_11_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_11(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_serialize_serialize_12(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[24U]) {
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(v.low, v.low));
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(v.low, v.low));
  uint8_t mixt = libcrux_intrinsics_arm64_extract__vsliq_n_s32(
      (int32_t)12, low00, low10, uint8_t);
  uint8_t low0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(mixt, mixt));
  uint8_t low1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(mixt, mixt));
  uint8_t low_mix = libcrux_intrinsics_arm64_extract__vsliq_n_s64(
      (int32_t)24, low0, low1, uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn1q_s16(v.high, v.high));
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
      libcrux_intrinsics_arm64_extract__vtrn2q_s16(v.high, v.high));
  uint8_t mixt0 = libcrux_intrinsics_arm64_extract__vsliq_n_s32(
      (int32_t)12, high00, high10, uint8_t);
  uint8_t high0 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn1q_s32(mixt0, mixt0));
  uint8_t high1 = libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
      libcrux_intrinsics_arm64_extract__vtrn2q_s32(mixt0, mixt0));
  uint8_t high_mix = libcrux_intrinsics_arm64_extract__vsliq_n_s64(
      (int32_t)24, high0, high1, uint8_t);
  uint8_t result32[32U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      result32, (size_t)0U, (size_t)16U, uint8_t, Eurydice_slice);
  libcrux_intrinsics_arm64_extract__vst1q_u8(
      uu____0, libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s64(low_mix));
  Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
      result32, (size_t)16U, (size_t)32U, uint8_t, Eurydice_slice);
  libcrux_intrinsics_arm64_extract__vst1q_u8(
      uu____1,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s64(high_mix));
  uint8_t result[24U] = {0U};
  Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
      result, (size_t)0U, (size_t)6U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_array_to_subslice2(result32, (size_t)0U, (size_t)6U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
      result, (size_t)6U, (size_t)12U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_array_to_subslice2(result32, (size_t)8U, (size_t)14U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice2(
      result, (size_t)12U, (size_t)18U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4,
      Eurydice_array_to_subslice2(result32, (size_t)16U, (size_t)22U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____5 = Eurydice_array_to_subslice2(
      result, (size_t)18U, (size_t)24U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____5,
      Eurydice_array_to_subslice2(result32, (size_t)24U, (size_t)30U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  memcpy(ret, result, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_12_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[24U]) {
  libcrux_ml_kem_vector_neon_serialize_serialize_12(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_12(Eurydice_slice v) {
  uint8_t indexes[16U] = {0U, 1U, 1U, 2U, 3U, 4U,  4U,  5U,
                          6U, 7U, 7U, 8U, 9U, 10U, 10U, 11U};
  uint8_t index_vec = libcrux_intrinsics_arm64_extract__vld1q_u8(
      Eurydice_array_to_slice((size_t)16U, indexes, uint8_t, Eurydice_slice));
  int16_t shifts[8U] = {(int16_t)0, (int16_t)-4, (int16_t)0, (int16_t)-4,
                        (int16_t)0, (int16_t)-4, (int16_t)0, (int16_t)-4};
  uint8_t shift_vec = libcrux_intrinsics_arm64_extract__vld1q_s16(
      Eurydice_array_to_slice((size_t)8U, shifts, int16_t, Eurydice_slice));
  uint8_t mask12 = libcrux_intrinsics_arm64_extract__vdupq_n_u16(4095U);
  uint8_t input0[16U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      input0, (size_t)0U, (size_t)12U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_slice_subslice2(v, (size_t)0U, (size_t)12U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  uint8_t input_vec0 = libcrux_intrinsics_arm64_extract__vld1q_u8(
      Eurydice_array_to_slice((size_t)16U, input0, uint8_t, Eurydice_slice));
  uint8_t input1[16U] = {0U};
  Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
      input1, (size_t)0U, (size_t)12U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____1,
      Eurydice_slice_subslice2(v, (size_t)12U, (size_t)24U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  uint8_t input_vec1 = libcrux_intrinsics_arm64_extract__vld1q_u8(
      Eurydice_array_to_slice((size_t)16U, input1, uint8_t, Eurydice_slice));
  uint8_t moved0 = libcrux_intrinsics_arm64_extract__vreinterpretq_u16_u8(
      libcrux_intrinsics_arm64_extract__vqtbl1q_u8(input_vec0, index_vec));
  uint8_t shifted0 =
      libcrux_intrinsics_arm64_extract__vshlq_u16(moved0, shift_vec);
  uint8_t low = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
      libcrux_intrinsics_arm64_extract__vandq_u16(shifted0, mask12));
  uint8_t moved1 = libcrux_intrinsics_arm64_extract__vreinterpretq_u16_u8(
      libcrux_intrinsics_arm64_extract__vqtbl1q_u8(input_vec1, index_vec));
  uint8_t shifted1 =
      libcrux_intrinsics_arm64_extract__vshlq_u16(moved1, shift_vec);
  uint8_t high = libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
      libcrux_intrinsics_arm64_extract__vandq_u16(shifted1, mask12));
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = low, .high = high});
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_12_20(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_12(a);
}

KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_neon_rej_sample(Eurydice_slice a, Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          core_slice___Slice_T___chunks(a, (size_t)3U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, core_slice_iter_Chunks);
  while (true) {
    core_option_Option_44 uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T___71__next(
            &iter, uint8_t, core_option_Option_44);
    if (uu____0.tag == core_option_None) {
      break;
    } else {
      Eurydice_slice bytes = uu____0.f0;
      int16_t b1 = (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t,
                                                 uint8_t *, uint8_t);
      int16_t b2 = (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t,
                                                 uint8_t *, uint8_t);
      int16_t b3 = (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t,
                                                 uint8_t *, uint8_t);
      int16_t d1 = (b2 & (int16_t)15) << 8U | b1;
      int16_t d2 = b3 << 4U | b2 >> 4U;
      bool uu____1;
      int16_t uu____2;
      bool uu____3;
      size_t uu____4;
      int16_t uu____5;
      size_t uu____6;
      int16_t uu____7;
      if (d1 < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
        if (sampled < (size_t)16U) {
          Eurydice_slice_index(result, sampled, int16_t, int16_t *, int16_t) =
              d1;
          sampled++;
          uu____2 = d2;
          uu____7 = LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
          uu____1 = uu____2 < uu____7;
          if (uu____1) {
            uu____4 = sampled;
            uu____3 = uu____4 < (size_t)16U;
            if (uu____3) {
              uu____5 = d2;
              uu____6 = sampled;
              Eurydice_slice_index(result, uu____6, int16_t, int16_t *,
                                   int16_t) = uu____5;
              sampled++;
              continue;
            }
          }
          continue;
        }
      }
      uu____2 = d2;
      uu____7 = LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
      uu____1 = uu____2 < uu____7;
      if (uu____1) {
        uu____4 = sampled;
        uu____3 = uu____4 < (size_t)16U;
        if (uu____3) {
          uu____5 = d2;
          uu____6 = sampled;
          Eurydice_slice_index(result, uu____6, int16_t, int16_t *, int16_t) =
              uu____5;
          sampled++;
          continue;
        }
      }
    }
  }
  return sampled;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
size_t libcrux_ml_kem_vector_neon_rej_sample_20(Eurydice_slice a,
                                                Eurydice_slice out) {
  return libcrux_ml_kem_vector_neon_rej_sample(a, out);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
inline libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_clone_ed(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1c ZERO_89_06(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c lit;
  lit.coefficients[0U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[1U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[2U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[3U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[4U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[5U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[6U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[7U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[8U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[9U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[10U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[11U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[12U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[13U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[14U] = libcrux_ml_kem_vector_neon_ZERO_20();
  lit.coefficients[15U] = libcrux_ml_kem_vector_neon_ZERO_20();
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_to_reduced_ring_element_e3(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_12_20(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_cond_subtract_3329_20(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 800
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a64(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
shift_right_8e(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  v.low = libcrux_intrinsics_arm64_extract__vshrq_n_s16((int32_t)15, v.low,
                                                        uint8_t);
  v.high = libcrux_intrinsics_arm64_extract__vshrq_n_s16((int32_t)15, v.high,
                                                         uint8_t);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.shift_right_20
with const generics
- SHIFT_BY= 15
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector shift_right_20_7d(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return shift_right_8e(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
to_unsigned_representative_64(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t = shift_right_20_7d(a);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector fm =
      libcrux_ml_kem_vector_neon_bitwise_and_with_constant_20(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_neon_add_20(a, &fm);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_77(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        to_unsigned_representative_64(re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_neon_serialize_12_20(coefficient, bytes);
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
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- OUT_LEN= 768
*/
static KRML_MUSTINLINE void serialize_secret_key_5d1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *key,
    uint8_t ret[768U]) {
  uint8_t out[768U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)2U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_77(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)768U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_701(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      public_key_serialized, (size_t)0U, (size_t)768U, uint8_t, Eurydice_slice);
  uint8_t ret0[768U];
  serialize_secret_key_5d1(t_as_ntt, ret0);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_7e1(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[2U];
  deserialize_ring_elements_reduced_a64(
      Eurydice_array_to_subslice_to((size_t)800U, public_key, (size_t)768U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key_701(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$2size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$2size_t]]

*/
typedef struct tuple_4c1_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66 fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 snd;
} tuple_4c1;

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_48
with const generics
- K= 2
*/
static KRML_MUSTINLINE void G_48_771(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_neon_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static void closure_de1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

typedef struct Simd128Hash_s {
  libcrux_sha3_generic_keccak_KeccakState_2c shake128_state[2U];
} Simd128Hash;

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb with const generics
- K= 2
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_6b1(uint8_t input[2U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_2c uu____0 =
      libcrux_sha3_neon_x2_incremental_shake128_init();
  libcrux_sha3_generic_keccak_KeccakState_2c state[2U] = {
      uu____0, libcrux_sha3_neon_x2_incremental_shake128_init()};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice));
  Simd128Hash lit;
  memcpy(lit.shake128_state, state,
         (size_t)2U * sizeof(libcrux_sha3_generic_keccak_KeccakState_2c));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_48 with const generics
- K= 2
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_48_551(uint8_t input[2U][34U]) {
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, input, (size_t)2U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_6b1(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks with const
generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_b71(
    Simd128Hash *st, uint8_t ret[2U][504U]) {
  uint8_t out[2U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  LowStar_Ignore_ignore(out2, uint8_t[504U], void *);
  uint8_t out3[504U] = {0U};
  LowStar_Ignore_ignore(out3, uint8_t[504U], void *);
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks_48 with const
generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_48_e91(
    Simd128Hash *self, uint8_t ret[2U][504U]) {
  shake128_squeeze_three_blocks_b71(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e63(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block with const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_block_7d1(Simd128Hash *st,
                                                       uint8_t ret[2U][168U]) {
  uint8_t out[2U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  LowStar_Ignore_ignore(out2, uint8_t[168U], void *);
  uint8_t out3[168U] = {0U};
  LowStar_Ignore_ignore(out3, uint8_t[168U], void *);
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block_48 with const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_block_48_ad1(
    Simd128Hash *self, uint8_t ret[2U][168U]) {
  shake128_squeeze_block_7d1(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e64(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
from_i16_array_89_f3(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.coefficients[i0] =
        libcrux_ml_kem_vector_neon_from_i16_array_20(Eurydice_slice_subslice2(
            a, i0 * (size_t)16U, (i0 + (size_t)1U) * (size_t)16U, int16_t,
            Eurydice_slice));
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1c closure_d51(
    int16_t s[272U]) {
  return from_i16_array_89_f3(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_from_xof_c01(
    uint8_t seeds[2U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  uint8_t uu____0[2U][34U];
  memcpy(uu____0, seeds, (size_t)2U * sizeof(uint8_t[34U]));
  Simd128Hash xof_state = shake128_init_absorb_48_551(uu____0);
  uint8_t randomness0[2U][504U];
  shake128_squeeze_three_blocks_48_e91(&xof_state, randomness0);
  uint8_t uu____1[2U][504U];
  memcpy(uu____1, randomness0, (size_t)2U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_e63(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      shake128_squeeze_block_48_ad1(&xof_state, randomness);
      uint8_t uu____2[2U][168U];
      memcpy(uu____2, randomness, (size_t)2U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_e64(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[2U][272U];
  memcpy(uu____3, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = closure_d51(uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_481(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U][2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  closure_de1(A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c sampled[2U];
      sample_from_xof_c01(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)2U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1c sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[2size_t], uint8_t

*/
typedef struct tuple_741_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c fst[2U];
  uint8_t snd;
} tuple_741;

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_891(uint8_t (*input)[33U],
                                      uint8_t ret[2U][192U]) {
  uint8_t out[2U][192U] = {{0U}};
  uint8_t out0[192U] = {0U};
  uint8_t out1[192U] = {0U};
  uint8_t out2[192U] = {0U};
  LowStar_Ignore_ignore(out2, uint8_t[192U], void *);
  uint8_t out3[192U] = {0U};
  LowStar_Ignore_ignore(out3, uint8_t[192U], void *);
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)192U, out1, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_48
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_48_a91(uint8_t (*input)[33U],
                                         uint8_t ret[2U][192U]) {
  PRFxN_891(input, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
sample_from_binomial_distribution_2_c3(Eurydice_slice randomness) {
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
  return from_i16_array_89_f3(Eurydice_array_to_slice(
      (size_t)256U, sampled_i16s, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
sample_from_binomial_distribution_3_27(Eurydice_slice randomness) {
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
  return from_i16_array_89_f3(Eurydice_array_to_slice(
      (size_t)256U, sampled_i16s, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
sample_from_binomial_distribution_2c0(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_27(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_67(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t =
        libcrux_ml_kem_vector_neon_multiply_by_constant_20(
            re->coefficients[j + step], (int16_t)-1600);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_sub_20(re->coefficients[j], &t);
    re->coefficients[j + step] = uu____0;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____1 =
        libcrux_ml_kem_vector_neon_add_20(re->coefficients[j], &t);
    re->coefficients[j] = uu____1;
  }
}

typedef struct libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2_s {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector fst;
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector snd;
} libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2;

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
montgomery_multiply_fe_91(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t fer) {
  return libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2
ntt_layer_int_vec_step_9c(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector b, int16_t zeta_r) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t =
      montgomery_multiply_fe_91(b, zeta_r);
  b = libcrux_ml_kem_vector_neon_sub_20(a, &t);
  a = libcrux_ml_kem_vector_neon_add_20(a, &t);
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2){
      .fst = a, .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_2a(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re,
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
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2 uu____0 =
          ntt_layer_int_vec_step_9c(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x = uu____0.fst;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_f4(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_ntt_layer_3_step_20(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      re->coefficients[round] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_d0(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_ntt_layer_2_step_20(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] +
                                                                 (size_t)1U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_39(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_ntt_layer_1_step_20(
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

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_89_5f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_20(self->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_cf(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  ntt_at_layer_7_67(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_f4(&zeta_i, re);
  ntt_at_layer_2_d0(&zeta_i, re);
  ntt_at_layer_1_39(&zeta_i, re);
  poly_barrett_reduce_89_5f(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE tuple_741 sample_vector_cbd_then_ntt_1f1(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_06(););
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
  PRFxN_48_a91(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c0(Eurydice_array_to_slice(
              (size_t)192U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_cf(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[2U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_741 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
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
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
ntt_multiply_89_16(libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c out = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_ntt_multiply_20(
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

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_89_ae1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)16U, self->coefficients,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
                   Eurydice_slice),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_20(self->coefficients[i0],
                                          &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
to_standard_domain_fc(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_89_ac(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form = to_standard_domain_fc(self->coefficients[j]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_20(
            libcrux_ml_kem_vector_neon_add_20(coefficient_normal_form,
                                              &error->coefficients[j]));
    self->coefficients[j] = uu____0;
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_As_plus_e_951(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)2U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_ae1(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static tuple_4c1 generate_keypair_unpacked_ff1(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_48_771(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[2U][2U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed_for_A0, ret);
  sample_matrix_A_481(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_741 uu____2 = sample_vector_cbd_then_ntt_1f1(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[2U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_as_ntt[2U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_1f1(uu____3, domain_separator).fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[2U];
  compute_As_plus_e_951(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____4[2U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[2U][2U];
  memcpy(uu____5, A_transpose,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____7[2U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66 sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  return (CLITERAL(tuple_4c1){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static void closure_891(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_d5
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1c clone_d5_13(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c lit;
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret,
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, void *);
  memcpy(lit.coefficients, ret,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_48
with const generics
- K= 2
*/
static KRML_MUSTINLINE void H_48_851(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_neon_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_b41(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_4c1 uu____0 = generate_keypair_unpacked_ff1(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, closure_891(A[i]););
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
              clone_d5_13(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[2U][2U];
  memcpy(uu____2, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  uint8_t pk_serialized[800U];
  serialize_public_key_701(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_48_851(Eurydice_array_to_slice((size_t)800U, pk_serialized, uint8_t,
                                   Eurydice_slice),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66 uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_66 uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66 lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair512 generate_keypair_161(
    Eurydice_slice key_generation_seed) {
  tuple_4c1 uu____0 = generate_keypair_unpacked_ff1(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66 sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 pk = uu____0.snd;
  uint8_t public_key_serialized[800U];
  serialize_public_key_701(pk.t_as_ntt,
                           Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                   uint8_t, Eurydice_slice),
                           public_key_serialized);
  uint8_t secret_key_serialized[768U];
  serialize_secret_key_5d1(sk.secret_as_ntt, secret_key_serialized);
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
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_d81(
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
  H_48_851(public_key, ret0);
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
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_ind_cca_generate_keypair_721(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_161(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key_d81(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[1632U];
  memcpy(uu____1, secret_key_serialized, (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_5e private_key =
      libcrux_ml_kem_types_from_05_e0(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_5e uu____2 = private_key;
  uint8_t uu____3[800U];
  memcpy(uu____3, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_2c(
      uu____2, libcrux_ml_kem_types_from_b6_57(uu____3));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_892(uint8_t (*input)[33U],
                                      uint8_t ret[2U][128U]) {
  uint8_t out[2U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  LowStar_Ignore_ignore(out2, uint8_t[128U], void *);
  uint8_t out3[128U] = {0U};
  LowStar_Ignore_ignore(out3, uint8_t[128U], void *);
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice));
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_48
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_48_a92(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_892(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
sample_from_binomial_distribution_2c(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_c3(randomness);
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_741
sample_ring_element_cbd_eb1(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  error_1[i] = ZERO_89_06(););
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
  PRFxN_48_a92(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[2U];
  memcpy(
      uu____2, error_1,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_741 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_b40(Eurydice_slice input, uint8_t ret[128U]) {
  uint8_t digest[128U] = {0U};
  uint8_t dummy[128U] = {0U};
  libcrux_sha3_neon_x2_shake256(
      input, input,
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, dummy, uint8_t, Eurydice_slice));
  memcpy(ret, digest, (size_t)128U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_48_6e4(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_b40(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_9b(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_20(
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

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_4b(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_20(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U] -
                                                                 (size_t)1U]);
      re->coefficients[round] = uu____0; zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_74(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_20(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      re->coefficients[round] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2
inv_ntt_layer_int_vec_step_reduce_27(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector b, int16_t zeta_r) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a_minus_b =
      libcrux_ml_kem_vector_neon_sub_20(b, &a);
  a = libcrux_ml_kem_vector_neon_barrett_reduce_20(
      libcrux_ml_kem_vector_neon_add_20(a, &b));
  b = montgomery_multiply_fe_91(a_minus_b, zeta_r);
  return (CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2){
      .fst = a, .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_fd(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re,
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
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2 uu____0 =
          inv_ntt_layer_int_vec_step_reduce_27(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[zeta_i[0U]]);
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x = uu____0.fst;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_621(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_9b(&zeta_i, re);
  invert_ntt_at_layer_2_4b(&zeta_i, re);
  invert_ntt_at_layer_3_74(&zeta_i, re);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_5f(re);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_89_24(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
                self->coefficients[j], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_20(
            libcrux_ml_kem_vector_neon_add_20(coefficient_normal_form,
                                              &error->coefficients[j]));
    self->coefficients[j] = uu____0;
  }
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_vector_u_6a1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)2U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_ae1(&result[i1], &product);
    }
    invert_ntt_montgomery_621(&result[i1]);
    add_error_reduce_89_24(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector decompress_1_fc(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_bitwise_and_with_constant_20(
      libcrux_ml_kem_vector_neon_sub_20(libcrux_ml_kem_vector_neon_ZERO_20(),
                                        &v),
      (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_message_23(uint8_t serialized[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
          coefficient_compressed = libcrux_ml_kem_vector_neon_deserialize_1_20(
              Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U, uint8_t,
                                          Eurydice_slice));
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          decompress_1_fc(coefficient_compressed);
      re.coefficients[i0] = uu____0;);
  return re;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
add_message_error_reduce_89_3a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
                result.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector tmp =
        libcrux_ml_kem_vector_neon_add_20(self->coefficients[i0],
                                          &message->coefficients[i0]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector tmp0 =
        libcrux_ml_kem_vector_neon_add_20(coefficient_normal_form, &tmp);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_20(tmp0);
    result.coefficients[i0] = uu____0;
  }
  return result;
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_ring_element_v_9b1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_ae1(&result, &product););
  invert_ntt_montgomery_621(&result);
  result = add_message_error_reduce_89_3a(error_2, message, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE uint8_t compress_int32x4_t_ce(uint8_t v) {
  uint8_t half = libcrux_intrinsics_arm64_extract__vdupq_n_u32(1664U);
  uint8_t compressed =
      libcrux_intrinsics_arm64_extract__vshlq_n_u32((int32_t)10, v, uint8_t);
  uint8_t compressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(compressed, half);
  uint8_t compressed1 = libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s32(
      libcrux_intrinsics_arm64_extract__vqdmulhq_n_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_u32(compressed0),
          (int32_t)10321340));
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)4, compressed1,
                                                       uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_fa(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask = libcrux_intrinsics_arm64_extract__vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)10));
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = compress_int32x4_t_ce(low00);
  uint8_t low1 = compress_int32x4_t_ce(low10);
  uint8_t high0 = compress_int32x4_t_ce(high00);
  uint8_t high1 = compress_int32x4_t_ce(high10);
  uint8_t low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  uint8_t high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  v.low = libcrux_intrinsics_arm64_extract__vandq_s16(low, mask);
  v.high = libcrux_intrinsics_arm64_extract__vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_20
with const generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_20_13(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_fa(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_ca0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_20_13(to_unsigned_representative_64(re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_neon_serialize_10_20(coefficient, bytes);
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
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE uint8_t compress_int32x4_t_ce0(uint8_t v) {
  uint8_t half = libcrux_intrinsics_arm64_extract__vdupq_n_u32(1664U);
  uint8_t compressed =
      libcrux_intrinsics_arm64_extract__vshlq_n_u32((int32_t)11, v, uint8_t);
  uint8_t compressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(compressed, half);
  uint8_t compressed1 = libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s32(
      libcrux_intrinsics_arm64_extract__vqdmulhq_n_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_u32(compressed0),
          (int32_t)10321340));
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)4, compressed1,
                                                       uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_fa0(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask = libcrux_intrinsics_arm64_extract__vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)11));
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = compress_int32x4_t_ce0(low00);
  uint8_t low1 = compress_int32x4_t_ce0(low10);
  uint8_t high0 = compress_int32x4_t_ce0(high00);
  uint8_t high1 = compress_int32x4_t_ce0(high10);
  uint8_t low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  uint8_t high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  v.low = libcrux_intrinsics_arm64_extract__vandq_s16(low, mask);
  v.high = libcrux_intrinsics_arm64_extract__vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_20
with const generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_20_130(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_fa0(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_840(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_ca0(re, uu____0);
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- OUT_LEN= 640
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static void compress_then_serialize_u_d71(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c input[2U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)2U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t,
        Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_840(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE uint8_t compress_int32x4_t_ce1(uint8_t v) {
  uint8_t half = libcrux_intrinsics_arm64_extract__vdupq_n_u32(1664U);
  uint8_t compressed =
      libcrux_intrinsics_arm64_extract__vshlq_n_u32((int32_t)4, v, uint8_t);
  uint8_t compressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(compressed, half);
  uint8_t compressed1 = libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s32(
      libcrux_intrinsics_arm64_extract__vqdmulhq_n_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_u32(compressed0),
          (int32_t)10321340));
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)4, compressed1,
                                                       uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_fa1(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask = libcrux_intrinsics_arm64_extract__vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)4));
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = compress_int32x4_t_ce1(low00);
  uint8_t low1 = compress_int32x4_t_ce1(low10);
  uint8_t high0 = compress_int32x4_t_ce1(high00);
  uint8_t high1 = compress_int32x4_t_ce1(high10);
  uint8_t low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  uint8_t high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  v.low = libcrux_intrinsics_arm64_extract__vandq_s16(low, mask);
  v.high = libcrux_intrinsics_arm64_extract__vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_20
with const generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_20_131(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_fa1(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_21(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_20_131(to_unsigned_representative_64(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_neon_serialize_4_20(coefficient, bytes);
    core_slice___Slice_T___copy_from_slice(
        Eurydice_slice_subslice2(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE uint8_t compress_int32x4_t_ce2(uint8_t v) {
  uint8_t half = libcrux_intrinsics_arm64_extract__vdupq_n_u32(1664U);
  uint8_t compressed =
      libcrux_intrinsics_arm64_extract__vshlq_n_u32((int32_t)5, v, uint8_t);
  uint8_t compressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(compressed, half);
  uint8_t compressed1 = libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s32(
      libcrux_intrinsics_arm64_extract__vqdmulhq_n_s32(
          libcrux_intrinsics_arm64_extract__vreinterpretq_s32_u32(compressed0),
          (int32_t)10321340));
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)4, compressed1,
                                                       uint8_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_fa2(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask = libcrux_intrinsics_arm64_extract__vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)5));
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = compress_int32x4_t_ce2(low00);
  uint8_t low1 = compress_int32x4_t_ce2(low10);
  uint8_t high0 = compress_int32x4_t_ce2(high00);
  uint8_t high1 = compress_int32x4_t_ce2(high10);
  uint8_t low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  uint8_t high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  v.low = libcrux_intrinsics_arm64_extract__vandq_s16(low, mask);
  v.high = libcrux_intrinsics_arm64_extract__vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_20
with const generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_20_132(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_fa2(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_2b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficients =
        compress_20_132(to_unsigned_representative_64(re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_neon_serialize_5_20(coefficients, bytes);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_3f0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re, Eurydice_slice out) {
  compress_then_serialize_4_21(re, out);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_unpacked_541(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_741 uu____1 = sample_vector_cbd_then_ntt_1f1(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_741 uu____3 = sample_ring_element_cbd_eb1(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[2U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_48_6e4(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_2 =
      sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u[2U];
  compute_vector_u_6a1(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message_as_ring_element =
      deserialize_then_decompress_message_23(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      compute_ring_element_v_9b1(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[768U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[2U];
  memcpy(
      uu____5, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  compress_then_serialize_u_d71(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)640U,
                                           uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____6 = v;
  compress_then_serialize_ring_element_v_3f0(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_unpacked_471(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_771(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_unpacked_541(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 =
      libcrux_ml_kem_types_from_01_20(uu____4);
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE void entropy_preprocess_af_c71(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 768
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a63(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_4e1(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[768U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[2U];
  deserialize_ring_elements_reduced_a63(
      Eurydice_slice_subslice_to(public_key, (size_t)768U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[2U][2U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed, ret0);
  sample_matrix_A_481(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[2U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1[2U][2U];
  memcpy(uu____1, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[2U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[768U];
  encrypt_unpacked_541(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)768U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE void kdf_af_631(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
tuple_ec libcrux_ml_kem_ind_cca_encapsulate_281(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_c71(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_48_851(Eurydice_array_to_slice(
               (size_t)800U, libcrux_ml_kem_types_as_slice_cb_1f(public_key),
               uint8_t, Eurydice_slice),
           ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_48_771(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_cb_1f(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[768U];
  encrypt_4e1(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[768U];
  memcpy(uu____4, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_e8 ciphertext0 =
      libcrux_ml_kem_types_from_01_20(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_631(shared_secret, shared_secret_array);
  libcrux_ml_kem_types_MlKemCiphertext_e8 uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_ec lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE uint8_t decompress_uint32x4_t_8f(uint8_t v) {
  uint8_t coeff = libcrux_intrinsics_arm64_extract__vdupq_n_u32(
      1U << (uint32_t)((int32_t)10 - (int32_t)1));
  uint8_t decompressed = libcrux_intrinsics_arm64_extract__vmulq_n_u32(
      v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t decompressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(decompressed, coeff);
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)10,
                                                       decompressed0, uint8_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_9c(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = decompress_uint32x4_t_8f(low00);
  uint8_t low1 = decompress_uint32x4_t_8f(low10);
  uint8_t high0 = decompress_uint32x4_t_8f(high00);
  uint8_t high1 = decompress_uint32x4_t_8f(high10);
  v.low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  v.high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_20 with const
generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_20_e8(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_9c(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_10_81(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)20U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_10_20(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_20_e8(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE uint8_t decompress_uint32x4_t_8f0(uint8_t v) {
  uint8_t coeff = libcrux_intrinsics_arm64_extract__vdupq_n_u32(
      1U << (uint32_t)((int32_t)11 - (int32_t)1));
  uint8_t decompressed = libcrux_intrinsics_arm64_extract__vmulq_n_u32(
      v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t decompressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(decompressed, coeff);
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)11,
                                                       decompressed0, uint8_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_9c0(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = decompress_uint32x4_t_8f0(low00);
  uint8_t low1 = decompress_uint32x4_t_8f0(low10);
  uint8_t high0 = decompress_uint32x4_t_8f0(high00);
  uint8_t high1 = decompress_uint32x4_t_8f0(high10);
  v.low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  v.high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_20 with const
generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_20_e80(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_9c0(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_11_6b(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)22U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)22U, i0 * (size_t)22U + (size_t)22U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_11_20(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_20_e80(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_ring_element_u_060(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_81(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_3c0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_f4(&zeta_i, re);
  ntt_at_layer_2_d0(&zeta_i, re);
  ntt_at_layer_1_39(&zeta_i, re);
  poly_barrett_reduce_89_5f(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_331(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_then_decompress_ring_element_u_060(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_3c0(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE uint8_t decompress_uint32x4_t_8f1(uint8_t v) {
  uint8_t coeff = libcrux_intrinsics_arm64_extract__vdupq_n_u32(
      1U << (uint32_t)((int32_t)4 - (int32_t)1));
  uint8_t decompressed = libcrux_intrinsics_arm64_extract__vmulq_n_u32(
      v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t decompressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(decompressed, coeff);
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)4,
                                                       decompressed0, uint8_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_9c1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = decompress_uint32x4_t_8f1(low00);
  uint8_t low1 = decompress_uint32x4_t_8f1(low10);
  uint8_t high0 = decompress_uint32x4_t_8f1(high00);
  uint8_t high1 = decompress_uint32x4_t_8f1(high10);
  v.low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  v.high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_20 with const
generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_20_e81(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_9c1(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_4_60(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)8U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_4_20(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_20_e81(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE uint8_t decompress_uint32x4_t_8f2(uint8_t v) {
  uint8_t coeff = libcrux_intrinsics_arm64_extract__vdupq_n_u32(
      1U << (uint32_t)((int32_t)5 - (int32_t)1));
  uint8_t decompressed = libcrux_intrinsics_arm64_extract__vmulq_n_u32(
      v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint8_t decompressed0 =
      libcrux_intrinsics_arm64_extract__vaddq_u32(decompressed, coeff);
  return libcrux_intrinsics_arm64_extract__vshrq_n_u32((int32_t)5,
                                                       decompressed0, uint8_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_9c2(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint8_t mask16 = libcrux_intrinsics_arm64_extract__vdupq_n_u32(65535U);
  uint8_t low00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), mask16);
  uint8_t low10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.low), uint8_t);
  uint8_t high00 = libcrux_intrinsics_arm64_extract__vandq_u32(
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), mask16);
  uint8_t high10 = libcrux_intrinsics_arm64_extract__vshrq_n_u32(
      (int32_t)16,
      libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(v.high), uint8_t);
  uint8_t low0 = decompress_uint32x4_t_8f2(low00);
  uint8_t low1 = decompress_uint32x4_t_8f2(low10);
  uint8_t high0 = decompress_uint32x4_t_8f2(high00);
  uint8_t high1 = decompress_uint32x4_t_8f2(high10);
  v.low = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(low1));
  v.high = libcrux_intrinsics_arm64_extract__vtrn1q_s16(
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high0),
      libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_20 with const
generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_20_e82(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_9c2(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_5_25(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)10U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)10U, i0 * (size_t)10U + (size_t)10U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_deserialize_5_20(bytes);
    re.coefficients[i0] = uu____0;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____1 =
        decompress_ciphertext_coefficient_20_e82(re.coefficients[i0]);
    re.coefficients[i0] = uu____1;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_ring_element_v_440(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_60(serialized);
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
subtract_reduce_89_25(libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1c b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
                b.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_20(
            libcrux_ml_kem_vector_neon_sub_20(self->coefficients[i0],
                                              &coefficient_normal_form));
    b.coefficients[i0] = uu____0;
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_message_c71(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_ae1(&result, &product););
  invert_ntt_montgomery_621(&result);
  result = subtract_reduce_89_25(v, result);
  return result;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
          to_unsigned_representative_64(re.coefficients[i0]);
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
          coefficient_compressed =
              libcrux_ml_kem_vector_neon_compress_1_20(coefficient);
      uint8_t bytes[2U];
      libcrux_ml_kem_vector_neon_serialize_1_20(coefficient_compressed, bytes);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_unpacked_d61(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[2U];
  deserialize_then_decompress_u_331(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      deserialize_then_decompress_ring_element_v_440(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message =
      compute_message_c71(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ab(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_b4(Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  uint8_t dummy[32U] = {0U};
  libcrux_sha3_neon_x2_shake256(
      input, input,
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, dummy, uint8_t, Eurydice_slice));
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 2
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_48_6e3(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_b4(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_ec1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66 *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_d61(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_771(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_970(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_f0(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_48_6e3(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_unpacked_541(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_f0(ciphertext),
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
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_to_uncompressed_ring_element_10(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = ZERO_89_06();
  for (size_t i = (size_t)0U;
       i <
       core_slice___Slice_T___len(serialized, uint8_t, size_t) / (size_t)24U;
       i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t,
        Eurydice_slice);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_deserialize_12_20(bytes);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_secret_key_4f1(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_uncompressed_ring_element_10(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_af1(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[2U];
  deserialize_secret_key_4f1(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[2U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t ret0[32U];
  decrypt_unpacked_d61(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
void libcrux_ml_kem_ind_cca_decapsulate_821(
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
  decrypt_af1(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_48_771(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_970(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_f0(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_48_6e3(
      Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[768U];
  encrypt_4e1(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_631(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_631(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_f0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 1184
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a62(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- OUT_LEN= 1152
*/
static KRML_MUSTINLINE void serialize_secret_key_5d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *key,
    uint8_t ret[1152U]) {
  uint8_t out[1152U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_77(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)1152U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_700(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(public_key_serialized, (size_t)0U,
                                  (size_t)1152U, uint8_t, Eurydice_slice);
  uint8_t ret0[1152U];
  serialize_secret_key_5d0(t_as_ntt, ret0);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_7e0(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[3U];
  deserialize_ring_elements_reduced_a62(
      Eurydice_array_to_subslice_to((size_t)1184U, public_key, (size_t)1152U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_700(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$3size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$3size_t]]

*/
typedef struct tuple_9b0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd snd;
} tuple_9b0;

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_48
with const generics
- K= 3
*/
static KRML_MUSTINLINE void G_48_770(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_neon_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static void closure_de0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb with const generics
- K= 3
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_6b0(uint8_t input[3U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_2c uu____0 =
      libcrux_sha3_neon_x2_incremental_shake128_init();
  libcrux_sha3_generic_keccak_KeccakState_2c state[2U] = {
      uu____0, libcrux_sha3_neon_x2_incremental_shake128_init()};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      &state[1U],
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice));
  Simd128Hash lit;
  memcpy(lit.shake128_state, state,
         (size_t)2U * sizeof(libcrux_sha3_generic_keccak_KeccakState_2c));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_48 with const generics
- K= 3
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_48_550(uint8_t input[3U][34U]) {
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, input, (size_t)3U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_6b0(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks with const
generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_b70(
    Simd128Hash *st, uint8_t ret[3U][504U]) {
  uint8_t out[3U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      &st->shake128_state[1U],
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks_48 with const
generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_48_e90(
    Simd128Hash *self, uint8_t ret[3U][504U]) {
  shake128_squeeze_three_blocks_b70(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e61(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block with const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_block_7d0(Simd128Hash *st,
                                                       uint8_t ret[3U][168U]) {
  uint8_t out[3U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      &st->shake128_state[1U],
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block_48 with const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_block_48_ad0(
    Simd128Hash *self, uint8_t ret[3U][168U]) {
  shake128_squeeze_block_7d0(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e62(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1c closure_d50(
    int16_t s[272U]) {
  return from_i16_array_89_f3(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_c00(
    uint8_t seeds[3U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  uint8_t uu____0[3U][34U];
  memcpy(uu____0, seeds, (size_t)3U * sizeof(uint8_t[34U]));
  Simd128Hash xof_state = shake128_init_absorb_48_550(uu____0);
  uint8_t randomness0[3U][504U];
  shake128_squeeze_three_blocks_48_e90(&xof_state, randomness0);
  uint8_t uu____1[3U][504U];
  memcpy(uu____1, randomness0, (size_t)3U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_e61(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      shake128_squeeze_block_48_ad0(&xof_state, randomness);
      uint8_t uu____2[3U][168U];
      memcpy(uu____2, randomness, (size_t)3U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_e62(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[3U][272U];
  memcpy(uu____3, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = closure_d50(uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_480(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  closure_de0(A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c sampled[3U];
      sample_from_xof_c00(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)3U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1c sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[3size_t], uint8_t

*/
typedef struct tuple_b00_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c fst[3U];
  uint8_t snd;
} tuple_b00;

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_890(uint8_t (*input)[33U],
                                      uint8_t ret[3U][128U]) {
  uint8_t out[3U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t, Eurydice_slice),
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_48
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_48_a90(uint8_t (*input)[33U],
                                         uint8_t ret[3U][128U]) {
  PRFxN_890(input, ret);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_b00 sample_vector_cbd_then_ntt_1f0(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_06(););
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
  PRFxN_48_a90(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_cf(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[3U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_b00 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_89_ae0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)16U, self->coefficients,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
                   Eurydice_slice),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_20(self->coefficients[i0],
                                          &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_950(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)3U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_ae0(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static tuple_9b0 generate_keypair_unpacked_ff0(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_48_770(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[3U][3U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed_for_A0, ret);
  sample_matrix_A_480(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____2 = sample_vector_cbd_then_ntt_1f0(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[3U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_as_ntt[3U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_1f0(uu____3, domain_separator).fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[3U];
  compute_As_plus_e_950(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____4[3U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[3U][3U];
  memcpy(uu____5, A_transpose,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____7[3U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  return (CLITERAL(tuple_9b0){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void closure_890(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_48
with const generics
- K= 3
*/
static KRML_MUSTINLINE void H_48_850(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_neon_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_b40(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_9b0 uu____0 = generate_keypair_unpacked_ff0(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, closure_890(A[i]););
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
              clone_d5_13(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[3U][3U];
  memcpy(uu____2, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  uint8_t pk_serialized[1184U];
  serialize_public_key_700(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_48_850(Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t,
                                   Eurydice_slice),
           public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_fd uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair768 generate_keypair_160(
    Eurydice_slice key_generation_seed) {
  tuple_9b0 uu____0 = generate_keypair_unpacked_ff0(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd pk = uu____0.snd;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_700(pk.t_as_ntt,
                           Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                   uint8_t, Eurydice_slice),
                           public_key_serialized);
  uint8_t secret_key_serialized[1152U];
  serialize_secret_key_5d0(sk.secret_as_ntt, secret_key_serialized);
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
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_d80(
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
  H_48_850(public_key, ret0);
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
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_720(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_160(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key_d80(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[2400U];
  memcpy(uu____1, secret_key_serialized, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 private_key =
      libcrux_ml_kem_types_from_05_e00(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_55 uu____2 = private_key;
  uint8_t uu____3[1184U];
  memcpy(uu____3, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_2c0(
      uu____2, libcrux_ml_kem_types_from_b6_570(uu____3));
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_b00
sample_ring_element_cbd_eb0(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  error_1[i] = ZERO_89_06(););
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
  PRFxN_48_a90(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[3U];
  memcpy(
      uu____2, error_1,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_b00 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_48_6e2(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_b40(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_620(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_9b(&zeta_i, re);
  invert_ntt_at_layer_2_4b(&zeta_i, re);
  invert_ntt_at_layer_3_74(&zeta_i, re);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_5f(re);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_6a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_ae0(&result[i1], &product);
    }
    invert_ntt_montgomery_620(&result[i1]);
    add_error_reduce_89_24(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_ring_element_v_9b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_ae0(&result, &product););
  invert_ntt_montgomery_620(&result);
  result = add_message_error_reduce_89_3a(error_2, message, result);
  return result;
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static void compress_then_serialize_u_d70(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t,
        Eurydice_slice);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_840(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)320U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_unpacked_540(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____1 = sample_vector_cbd_then_ntt_1f0(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_b00 uu____3 = sample_ring_element_cbd_eb0(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[3U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_48_6e2(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_2 =
      sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u[3U];
  compute_vector_u_6a0(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message_as_ring_element =
      deserialize_then_decompress_message_23(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      compute_ring_element_v_9b0(public_key->t_as_ntt, r_as_ntt, &error_2,
                                 &message_as_ring_element);
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[3U];
  memcpy(
      uu____5, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  compress_then_serialize_u_d70(
      uu____5, Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                           uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____6 = v;
  compress_then_serialize_ring_element_v_3f0(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_unpacked_470(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_fd *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_770(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_unpacked_540(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 =
      libcrux_ml_kem_types_from_01_200(uu____4);
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_af_c70(Eurydice_slice randomness,
                                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 1152
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a61(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_4e0(Eurydice_slice public_key, uint8_t message[32U],
                        Eurydice_slice randomness, uint8_t ret[1088U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[3U];
  deserialize_ring_elements_reduced_a61(
      Eurydice_slice_subslice_to(public_key, (size_t)1152U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[3U][3U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed, ret0);
  sample_matrix_A_480(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[3U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1[3U][3U];
  memcpy(uu____1, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[3U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1088U];
  encrypt_unpacked_540(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void kdf_af_630(Eurydice_slice shared_secret,
                                       uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
tuple_3c libcrux_ml_kem_ind_cca_encapsulate_280(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_c70(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_48_850(Eurydice_array_to_slice(
               (size_t)1184U, libcrux_ml_kem_types_as_slice_cb_1f0(public_key),
               uint8_t, Eurydice_slice),
           ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_48_770(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_cb_1f0(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1088U];
  encrypt_4e0(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1088U];
  memcpy(uu____4, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_01_200(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_630(shared_secret, shared_secret_array);
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____5 = ciphertext0;
  uint8_t uu____6[32U];
  memcpy(uu____6, shared_secret_array, (size_t)32U * sizeof(uint8_t));
  tuple_3c lit;
  lit.fst = uu____5;
  memcpy(lit.snd, uu____6, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_330(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_then_decompress_ring_element_u_060(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_3c0(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_message_c70(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_ae0(&result, &product););
  invert_ntt_montgomery_620(&result);
  result = subtract_reduce_89_25(v, result);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_unpacked_d60(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[3U];
  deserialize_then_decompress_u_330(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      deserialize_then_decompress_ring_element_v_440(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message =
      compute_message_c70(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ab(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 3
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_48_6e1(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_b4(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_ec0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_d60(&key_pair->private_key.ind_cpa_private_key,
                       ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_770(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_973(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_f00(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_48_6e1(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_unpacked_540(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_f00(ciphertext),
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
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_secret_key_4f0(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_uncompressed_ring_element_10(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static void decrypt_af0(Eurydice_slice secret_key, uint8_t *ciphertext,
                        uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[3U];
  deserialize_secret_key_4f0(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[3U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t ret0[32U];
  decrypt_unpacked_d60(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
void libcrux_ml_kem_ind_cca_decapsulate_820(
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
  decrypt_af0(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_48_770(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_973(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_f00(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_48_6e1(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1088U];
  encrypt_4e0(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_630(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_630(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_f00(ciphertext),
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
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 1568
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a60(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- OUT_LEN= 1536
*/
static KRML_MUSTINLINE void serialize_secret_key_5d(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *key,
    uint8_t ret[1536U]) {
  uint8_t out[1536U] = {0U};
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = key[i0];
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t, Eurydice_slice);
    uint8_t ret0[384U];
    serialize_uncompressed_ring_element_77(&re, ret0);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)384U, ret0, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  memcpy(ret, out, (size_t)1536U * sizeof(uint8_t));
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_70(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(public_key_serialized, (size_t)0U,
                                  (size_t)1536U, uint8_t, Eurydice_slice);
  uint8_t ret0[1536U];
  serialize_secret_key_5d(t_as_ntt, ret0);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_7e(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[4U];
  deserialize_ring_elements_reduced_a60(
      Eurydice_array_to_subslice_to((size_t)1568U, public_key, (size_t)1536U,
                                    uint8_t, size_t, Eurydice_slice),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_70(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$4size_t]],
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$4size_t]]

*/
typedef struct tuple_54_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c snd;
} tuple_54;

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_48
with const generics
- K= 4
*/
static KRML_MUSTINLINE void G_48_77(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_neon_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A.closure
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static void closure_de(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb with const generics
- K= 4
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_6b(uint8_t input[4U][34U]) {
  libcrux_sha3_generic_keccak_KeccakState_2c uu____0 =
      libcrux_sha3_neon_x2_incremental_shake128_init();
  libcrux_sha3_generic_keccak_KeccakState_2c state[2U] = {
      uu____0, libcrux_sha3_neon_x2_incremental_shake128_init()};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state,
      Eurydice_array_to_slice((size_t)34U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[1U], uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      &state[1U],
      Eurydice_array_to_slice((size_t)34U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)34U, input[3U], uint8_t, Eurydice_slice));
  Simd128Hash lit;
  memcpy(lit.shake128_state, state,
         (size_t)2U * sizeof(libcrux_sha3_generic_keccak_KeccakState_2c));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_48 with const generics
- K= 4
*/
static KRML_MUSTINLINE Simd128Hash
shake128_init_absorb_48_55(uint8_t input[4U][34U]) {
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, input, (size_t)4U * sizeof(uint8_t[34U]));
  return shake128_init_absorb_6b(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks with const
generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_b7(
    Simd128Hash *st, uint8_t ret[4U][504U]) {
  uint8_t out[4U][504U] = {{0U}};
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)504U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      &st->shake128_state[1U],
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_three_blocks_48 with const
generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_three_blocks_48_e9(
    Simd128Hash *self, uint8_t ret[4U][504U]) {
  shake128_squeeze_three_blocks_b7(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e6(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block with const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_block_7d(Simd128Hash *st,
                                                      uint8_t ret[4U][168U]) {
  uint8_t out[4U][168U] = {{0U}};
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->shake128_state,
      Eurydice_array_to_slice((size_t)168U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      &st->shake128_state[1U],
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_block_48 with const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_block_48_ad(
    Simd128Hash *self, uint8_t ret[4U][168U]) {
  shake128_squeeze_block_7d(self, ret);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_e60(
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
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_20(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1c closure_d5(
    int16_t s[272U]) {
  return from_i16_array_89_f3(Eurydice_array_to_subslice2(
      s, (size_t)0U, (size_t)256U, int16_t, Eurydice_slice));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_c0(
    uint8_t seeds[4U][34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  uint8_t uu____0[4U][34U];
  memcpy(uu____0, seeds, (size_t)4U * sizeof(uint8_t[34U]));
  Simd128Hash xof_state = shake128_init_absorb_48_55(uu____0);
  uint8_t randomness0[4U][504U];
  shake128_squeeze_three_blocks_48_e9(&xof_state, randomness0);
  uint8_t uu____1[4U][504U];
  memcpy(uu____1, randomness0, (size_t)4U * sizeof(uint8_t[504U]));
  bool done = sample_from_uniform_distribution_next_e6(
      uu____1, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      shake128_squeeze_block_48_ad(&xof_state, randomness);
      uint8_t uu____2[4U][168U];
      memcpy(uu____2, randomness, (size_t)4U * sizeof(uint8_t[168U]));
      done = sample_from_uniform_distribution_next_e60(
          uu____2, sampled_coefficients, out);
    }
  }
  int16_t uu____3[4U][272U];
  memcpy(uu____3, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = closure_d5(uu____3[i]););
  memcpy(
      ret, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_48(
    uint8_t seed[34U], bool transpose,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U][4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  closure_de(A_transpose[i]););
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
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c sampled[4U];
      sample_from_xof_c0(uu____1, sampled);
      for (size_t i = (size_t)0U;
           i < core_slice___Slice_T___len(
                   Eurydice_array_to_slice(
                       (size_t)4U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                       Eurydice_slice),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1c sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
  memcpy(ret, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[4size_t], uint8_t

*/
typedef struct tuple_71_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c fst[4U];
  uint8_t snd;
} tuple_71;

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_89(uint8_t (*input)[33U],
                                     uint8_t ret[4U][128U]) {
  uint8_t out[4U][128U] = {{0U}};
  uint8_t out0[128U] = {0U};
  uint8_t out1[128U] = {0U};
  uint8_t out2[128U] = {0U};
  uint8_t out3[128U] = {0U};
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[0U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[1U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)128U, out1, uint8_t, Eurydice_slice));
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input[2U], uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)33U, input[3U], uint8_t, Eurydice_slice),
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_48
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_48_a9(uint8_t (*input)[33U],
                                        uint8_t ret[4U][128U]) {
  PRFxN_89(input, ret);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_71 sample_vector_cbd_then_ntt_1f(
    uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c re_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  re_as_ntt[i] = ZERO_89_06(););
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
  PRFxN_48_a9(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      re_as_ntt[i0] = uu____1;
      ntt_binomially_sampled_ring_element_cf(&re_as_ntt[i0]););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[4U];
  memcpy(
      uu____2, re_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_71 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_89
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_89_ae(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *rhs) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)16U, self->coefficients,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
                   Eurydice_slice),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_20(self->coefficients[i0],
                                          &rhs->coefficients[i0]);
    self->coefficients[i0] = uu____0;
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_95(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)4U, matrix_A,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = matrix_A[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_89_ae(&result[i1], &product);
    }
    add_standard_error_reduce_89_ac(&result[i1], &error_as_ntt[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static tuple_54 generate_keypair_unpacked_ff(
    Eurydice_slice key_generation_seed) {
  uint8_t hashed[64U];
  G_48_77(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      (size_t)32U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A0 = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A_transpose[4U][4U];
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed_for_A0, ret);
  sample_matrix_A_48(ret, true, A_transpose);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(seed_for_secret_and_error,
                                             prf_input);
  uint8_t uu____1[33U];
  memcpy(uu____1, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____2 = sample_vector_cbd_then_ntt_1f(uu____1, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[4U];
  memcpy(
      secret_as_ntt, uu____2.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____2.snd;
  uint8_t uu____3[33U];
  memcpy(uu____3, prf_input, (size_t)33U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_as_ntt[4U];
  memcpy(
      error_as_ntt,
      sample_vector_cbd_then_ntt_1f(uu____3, domain_separator).fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[4U];
  compute_As_plus_e_95(A_transpose, secret_as_ntt, error_as_ntt, t_as_ntt);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A0, Eurydice_slice, uint8_t[32U],
                           void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____4[4U];
  memcpy(
      uu____4, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[4U][4U];
  memcpy(uu____5, A_transpose,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  uint8_t uu____6[32U];
  memcpy(uu____6, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c pk;
  memcpy(
      pk.t_as_ntt, uu____4,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(pk.seed_for_A, uu____6, (size_t)32U * sizeof(uint8_t));
  memcpy(pk.A, uu____5,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____7[4U];
  memcpy(
      uu____7, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c sk;
  memcpy(
      sk.secret_as_ntt, uu____7,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  return (CLITERAL(tuple_54){.fst = sk, .snd = pk});
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.generate_keypair_unpacked.closure with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void closure_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret[i] = ZERO_89_06(););
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_48
with const generics
- K= 4
*/
static KRML_MUSTINLINE void H_48_85(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_neon_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_b4(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value0 = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  tuple_54 uu____0 = generate_keypair_unpacked_ff(ind_cpa_keypair_randomness);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c
      ind_cpa_private_key = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c
      ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, closure_89(A[i]););
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
              clone_d5_13(&ind_cpa_public_key.A[j][i1]);
          A[i1][j] = uu____1;););
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[4U][4U];
  memcpy(uu____2, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  memcpy(ind_cpa_public_key.A, uu____2,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  uint8_t pk_serialized[1568U];
  serialize_public_key_70(
      ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, ind_cpa_public_key.seed_for_A,
                              uint8_t, Eurydice_slice),
      pk_serialized);
  uint8_t public_key_hash[32U];
  H_48_85(Eurydice_array_to_slice((size_t)1568U, pk_serialized, uint8_t,
                                  Eurydice_slice),
          public_key_hash);
  uint8_t implicit_rejection_value[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value0, Eurydice_slice,
                           uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, implicit_rejection_value);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c uu____3 =
      ind_cpa_private_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, implicit_rejection_value, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_2c uu____5;
  uu____5.ind_cpa_private_key = uu____3;
  memcpy(uu____5.implicit_rejection_value, uu____4,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c uu____6 =
      ind_cpa_public_key;
  uint8_t uu____7[32U];
  memcpy(uu____7, public_key_hash, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c lit;
  lit.private_key = uu____5;
  lit.public_key.ind_cpa_public_key = uu____6;
  memcpy(lit.public_key.public_key_hash, uu____7,
         (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair1024 generate_keypair_16(
    Eurydice_slice key_generation_seed) {
  tuple_54 uu____0 = generate_keypair_unpacked_ff(key_generation_seed);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c sk = uu____0.fst;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c pk = uu____0.snd;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_70(pk.t_as_ntt,
                          Eurydice_array_to_slice((size_t)32U, pk.seed_for_A,
                                                  uint8_t, Eurydice_slice),
                          public_key_serialized);
  uint8_t secret_key_serialized[1536U];
  serialize_secret_key_5d(sk.secret_as_ntt, secret_key_serialized);
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
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_d8(
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
  H_48_85(public_key, ret0);
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
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_72(uint8_t randomness[64U]) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      Eurydice_slice);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, Eurydice_slice);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_16(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key_d8(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t,
                              Eurydice_slice),
      implicit_rejection_value, secret_key_serialized);
  uint8_t uu____1[3168U];
  memcpy(uu____1, secret_key_serialized, (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_95 private_key =
      libcrux_ml_kem_types_from_05_e01(uu____1);
  libcrux_ml_kem_types_MlKemPrivateKey_95 uu____2 = private_key;
  uint8_t uu____3[1568U];
  memcpy(uu____3, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_2c1(
      uu____2, libcrux_ml_kem_types_from_b6_571(uu____3));
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE tuple_71
sample_ring_element_cbd_eb(uint8_t prf_input[33U], uint8_t domain_separator) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  error_1[i] = ZERO_89_06(););
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
  PRFxN_48_a9(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1 =
          sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
              (size_t)128U, prf_outputs[i0], uint8_t, Eurydice_slice));
      error_1[i0] = uu____1;);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____2[4U];
  memcpy(
      uu____2, error_1,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  tuple_71 lit;
  memcpy(
      lit.fst, uu____2,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  lit.snd = domain_separator;
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_48_6e0(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_b40(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_62(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_9b(&zeta_i, re);
  invert_ntt_at_layer_2_4b(&zeta_i, re);
  invert_ntt_at_layer_3_74(&zeta_i, re);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_fd(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_89_5f(re);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_6a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  result[i] = ZERO_89_06(););
  for (size_t i0 = (size_t)0U;
       i0 < core_slice___Slice_T___len(
                Eurydice_array_to_slice(
                    (size_t)4U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U],
                    Eurydice_slice),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U], size_t);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < core_slice___Slice_T___len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                     Eurydice_slice),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
          ntt_multiply_89_16(a_element, &r_as_ntt[j]);
      add_to_ring_element_89_ae(&result[i1], &product);
    }
    invert_ntt_montgomery_62(&result[i1]);
    add_error_reduce_89_24(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_ring_element_v_9b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_89_ae(&result, &product););
  invert_ntt_montgomery_62(&result);
  result = add_message_error_reduce_89_3a(error_2, message, result);
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_55(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_20_130(to_unsigned_representative_64(re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_neon_serialize_11_20(coefficient, bytes);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_84(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_55(re, uu____0);
  memcpy(ret, uu____0, (size_t)352U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- OUT_LEN= 1408
- COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static void compress_then_serialize_u_d7(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c input[4U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1c,
                   Eurydice_slice),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1c, size_t);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t,
        Eurydice_slice);
    uint8_t ret[352U];
    compress_then_serialize_ring_element_u_84(&re, ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)352U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_3f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c re, Eurydice_slice out) {
  compress_then_serialize_5_2b(re, out);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_unpacked_54(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c *public_key,
    uint8_t message[32U], Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_972(randomness, prf_input);
  uint8_t uu____0[33U];
  memcpy(uu____0, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____1 = sample_vector_cbd_then_ntt_1f(uu____0, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____1.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator0 = uu____1.snd;
  uint8_t uu____2[33U];
  memcpy(uu____2, prf_input, (size_t)33U * sizeof(uint8_t));
  tuple_71 uu____3 = sample_ring_element_cbd_eb(uu____2, domain_separator0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_1[4U];
  memcpy(
      error_1, uu____3.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t domain_separator = uu____3.snd;
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_48_6e0(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t, Eurydice_slice),
      prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c error_2 =
      sample_from_binomial_distribution_2c(Eurydice_array_to_slice(
          (size_t)128U, prf_output, uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u[4U];
  compute_vector_u_6a(public_key->A, r_as_ntt, error_1, u);
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message_as_ring_element =
      deserialize_then_decompress_message_23(uu____4);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      compute_ring_element_v_9b(public_key->t_as_ntt, r_as_ntt, &error_2,
                                &message_as_ring_element);
  uint8_t ciphertext[1568U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____5[4U];
  memcpy(
      uu____5, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  compress_then_serialize_u_d7(
      uu____5,
      Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)1408U,
                                  uint8_t, Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____6 = v;
  compress_then_serialize_ring_element_v_3f(
      uu____6,
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, Eurydice_slice));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_unpacked_47(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_2c *public_key,
    uint8_t randomness[32U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_77(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c *uu____2 =
      &public_key->ind_cpa_public_key;
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_unpacked_54(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t,
                              Eurydice_slice),
      shared_secret, uint8_t, void *);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____5 =
      libcrux_ml_kem_types_from_01_201(uu____4);
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_af_c7(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      randomness, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- PUBLIC_KEY_SIZE= 1536
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a6(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  deserialized_pk[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_reduced_ring_element_e3(ring_element);
    deserialized_pk[i0] = uu____0;
  }
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
static void encrypt_4e(Eurydice_slice public_key, uint8_t message[32U],
                       Eurydice_slice randomness, uint8_t ret[1568U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[4U];
  deserialize_ring_elements_reduced_a6(
      Eurydice_slice_subslice_to(public_key, (size_t)1536U, uint8_t, size_t,
                                 Eurydice_slice),
      t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, Eurydice_slice);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[4U][4U];
  uint8_t ret0[34U];
  libcrux_ml_kem_utils_into_padded_array_971(seed, ret0);
  sample_matrix_A_48(ret0, false, A);
  uint8_t seed_for_A[32U];
  core_result_Result_00 dst;
  Eurydice_slice_to_array2(&dst, seed, Eurydice_slice, uint8_t[32U], void *);
  core_result_unwrap_41_83(dst, seed_for_A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[4U];
  memcpy(
      uu____0, t_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____1[4U][4U];
  memcpy(uu____1, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  uint8_t uu____2[32U];
  memcpy(uu____2, seed_for_A, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c
      public_key_unpacked;
  memcpy(
      public_key_unpacked.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  memcpy(public_key_unpacked.seed_for_A, uu____2,
         (size_t)32U * sizeof(uint8_t));
  memcpy(public_key_unpacked.A, uu____1,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c[4U]));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c *uu____3 =
      &public_key_unpacked;
  uint8_t uu____4[32U];
  memcpy(uu____4, message, (size_t)32U * sizeof(uint8_t));
  uint8_t ret1[1568U];
  encrypt_unpacked_54(uu____3, uu____4, randomness, ret1);
  memcpy(ret, ret1, (size_t)1568U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::ind_cca::Variant for
libcrux_ml_kem::ind_cca::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.kdf_af
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE void kdf_af_63(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice),
      shared_secret, uint8_t, void *);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
tuple_21 libcrux_ml_kem_ind_cca_encapsulate_28(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  uint8_t randomness0[32U];
  entropy_preprocess_af_c7(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t, Eurydice_slice),
      randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t,
                              Eurydice_slice),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, Eurydice_slice);
  uint8_t ret[32U];
  H_48_85(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_cb_1f1(public_key),
              uint8_t, Eurydice_slice),
          ret);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, ret, uint8_t, Eurydice_slice),
      uint8_t, void *);
  uint8_t hashed[64U];
  G_48_77(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_cb_1f1(public_key), uint8_t,
      Eurydice_slice);
  uint8_t uu____3[32U];
  memcpy(uu____3, randomness0, (size_t)32U * sizeof(uint8_t));
  uint8_t ciphertext[1568U];
  encrypt_4e(uu____2, uu____3, pseudorandomness, ciphertext);
  uint8_t uu____4[1568U];
  memcpy(uu____4, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext ciphertext0 =
      libcrux_ml_kem_types_from_01_201(uu____4);
  uint8_t shared_secret_array[32U];
  kdf_af_63(shared_secret, shared_secret_array);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_ring_element_u_06(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_6b(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_3c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_2a(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_f4(&zeta_i, re);
  ntt_at_layer_2_d0(&zeta_i, re);
  ntt_at_layer_1_39(&zeta_i, re);
  poly_barrett_reduce_89_5f(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_33(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  u_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_then_decompress_ring_element_u_06(u_bytes);
    u_as_ntt[i0] = uu____0;
    ntt_vector_u_3c(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
deserialize_then_decompress_ring_element_v_44(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_25(serialized);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1c
compute_message_c7(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c result = ZERO_89_06();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1c product =
                      ntt_multiply_89_16(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_89_ae(&result, &product););
  invert_ntt_montgomery_62(&result);
  result = subtract_reduce_89_25(v, result);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static void decrypt_unpacked_d6(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c u_as_ntt[4U];
  deserialize_then_decompress_u_33(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c v =
      deserialize_then_decompress_ring_element_v_44(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t,
                                          Eurydice_slice));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c message =
      compute_message_c7(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ab(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_48
with const generics
- K= 4
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_48_6e(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_b4(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
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
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_ec(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_d6(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
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
  G_48_77(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_974(
      Eurydice_array_to_slice((size_t)32U,
                              key_pair->private_key.implicit_rejection_value,
                              uint8_t, Eurydice_slice),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2, libcrux_ml_kem_types_as_ref_00_f01(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_48_6e(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c *uu____3 =
      &key_pair->public_key.ind_cpa_public_key;
  uint8_t uu____4[32U];
  memcpy(uu____4, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_unpacked_54(uu____3, uu____4, pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_00_f01(ciphertext),
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
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_secret_key_4f(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  secret_as_ntt[i] = ZERO_89_06(););
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0 =
        deserialize_to_uncompressed_ring_element_10(secret_bytes);
    secret_as_ntt[i0] = uu____0;
  }
  memcpy(
      ret, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static void decrypt_af(Eurydice_slice secret_key, uint8_t *ciphertext,
                       uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[4U];
  deserialize_secret_key_4f(secret_key, secret_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c uu____0[4U];
  memcpy(
      uu____0, secret_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c
      secret_key_unpacked;
  memcpy(
      secret_key_unpacked.secret_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1c));
  uint8_t ret0[32U];
  decrypt_unpacked_d6(&secret_key_unpacked, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem
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
void libcrux_ml_kem_ind_cca_decapsulate_82(
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
  decrypt_af(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_97(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t, Eurydice_slice),
      to_hash0);
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, Eurydice_slice),
      ind_cpa_public_key_hash, uint8_t, void *);
  uint8_t hashed[64U];
  G_48_77(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t, Eurydice_slice),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t, Eurydice_slice),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____3.fst;
  Eurydice_slice pseudorandomness = uu____3.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_974(implicit_rejection_value, to_hash);
  Eurydice_slice uu____4 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____4, libcrux_ml_kem_types_as_ref_00_f01(ciphertext), uint8_t, void *);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_48_6e(
      Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret0);
  Eurydice_slice uu____5 = ind_cpa_public_key;
  uint8_t uu____6[32U];
  memcpy(uu____6, decrypted, (size_t)32U * sizeof(uint8_t));
  uint8_t expected_ciphertext[1568U];
  encrypt_4e(uu____5, uu____6, pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_af_63(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t, Eurydice_slice),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_af_63(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_00_f01(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t,
                              Eurydice_slice),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t, Eurydice_slice),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}
