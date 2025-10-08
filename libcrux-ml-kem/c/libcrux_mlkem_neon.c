/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: c66a520f7072006af0071eb517002a73d5f3a7d1
 * Eurydice: 9dae7cbf24d38b7b0eb8e7efd12d662a4ebe1f1a
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: fba8ff3916a9aa0a3869f2fffea66d8aea07144a
 */

#include "internal/libcrux_mlkem_neon.h"

#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"
#include "internal/libcrux_sha3_neon.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"
#include "libcrux_sha3_neon.h"
#include "libcrux_sha3_portable.h"

KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input) {
  libcrux_sha3_Sha3_512Digest digest = {.data = {0U}};
  libcrux_sha3_neon_sha512(
      Eurydice_array_to_slice((size_t)64U, &digest, uint8_t), input);
  return digest;
}

KRML_MUSTINLINE Eurydice_arr_60
libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  libcrux_sha3_neon_sha256(
      Eurydice_array_to_slice((size_t)32U, &digest, uint8_t), input);
  return digest;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_ZERO(void) {
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vdupq_n_s16((int16_t)0), .high = _vdupq_n_s16((int16_t)0)});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ZERO_61(void) {
  return libcrux_ml_kem_vector_neon_vector_type_ZERO();
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_i16_array(Eurydice_slice array) {
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_s16(
          Eurydice_slice_subslice3(array, (size_t)0U, (size_t)8U, int16_t *)),
      .high = _vld1q_s16(Eurydice_slice_subslice3(array, (size_t)8U,
                                                  (size_t)16U, int16_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_i16_array_61(Eurydice_slice array) {
  return libcrux_ml_kem_vector_neon_vector_type_from_i16_array(array);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_neon_vector_type_to_i16_array(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  Eurydice_arr_e2 out = {.data = {0U}};
  _vst1q_s16(
      Eurydice_array_to_subslice3(&out, (size_t)0U, (size_t)8U, int16_t *),
      v.low);
  _vst1q_s16(
      Eurydice_array_to_subslice3(&out, (size_t)8U, (size_t)16U, int16_t *),
      v.high);
  return out;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_neon_to_i16_array_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x) {
  return libcrux_ml_kem_vector_neon_vector_type_to_i16_array(x);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_bytes(Eurydice_slice array) {
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_bytes(
          Eurydice_slice_subslice3(array, (size_t)0U, (size_t)16U, uint8_t *)),
      .high = _vld1q_bytes(Eurydice_slice_subslice3(array, (size_t)16U,
                                                    (size_t)32U, uint8_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_bytes_61(Eurydice_slice array) {
  return libcrux_ml_kem_vector_neon_vector_type_from_bytes(array);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_neon_vector_type_to_bytes(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
    Eurydice_slice bytes) {
  _vst1q_bytes(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)16U, uint8_t *),
      v.low);
  _vst1q_bytes(
      Eurydice_slice_subslice3(bytes, (size_t)16U, (size_t)32U, uint8_t *),
      v.high);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
void libcrux_ml_kem_vector_neon_to_bytes_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x,
    Eurydice_slice bytes) {
  libcrux_ml_kem_vector_neon_vector_type_to_bytes(x, bytes);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_add(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  lhs.low = _vaddq_s16(lhs.low, rhs->low);
  lhs.high = _vaddq_s16(lhs.high, rhs->high);
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_add_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  return libcrux_ml_kem_vector_neon_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_sub(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  lhs.low = _vsubq_s16(lhs.low, rhs->low);
  lhs.high = _vsubq_s16(lhs.high, rhs->high);
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_sub_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs) {
  return libcrux_ml_kem_vector_neon_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  v.low = _vmulq_n_s16(v.low, c);
  v.high = _vmulq_n_s16(v.high, c);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_multiply_by_constant_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  return libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(v, c);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t c = _vdupq_n_s16((int16_t)3329);
  uint16x8_t m0 = _vcgeq_s16(v.low, c);
  uint16x8_t m1 = _vcgeq_s16(v.high, c);
  int16x8_t c0 = _vandq_s16(c, _vreinterpretq_s16_u16(m0));
  int16x8_t c1 = _vandq_s16(c, _vreinterpretq_s16_u16(m1));
  v.low = _vsubq_s16(v.low, c0);
  v.high = _vsubq_s16(v.high, c1);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_cond_subtract_3329_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(v);
}

KRML_MUSTINLINE int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(int16x8_t v) {
  int16x8_t adder = _vdupq_n_s16((int16_t)1024);
  int16x8_t vec = _vqdmulhq_n_s16(
      v, LIBCRUX_ML_KEM_VECTOR_NEON_ARITHMETIC_BARRETT_MULTIPLIER);
  int16x8_t vec0 = _vaddq_s16(vec, adder);
  int16x8_t quotient = _vshrq_n_s16((int32_t)11, vec0, int16x8_t);
  int16x8_t sub =
      _vmulq_n_s16(quotient, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return _vsubq_s16(v, sub);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_barrett_reduce_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce(v);
}

KRML_MUSTINLINE int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
    int16x8_t low, int16x8_t high) {
  int16x8_t k = _vreinterpretq_s16_u16(_vmulq_n_u16(
      _vreinterpretq_u16_s16(low),
      (uint16_t)
          LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  int16x8_t c = _vshrq_n_s16(
      (int32_t)1,
      _vqdmulhq_n_s16(k, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS),
      int16x8_t);
  return _vsubq_s16(high, c);
}

KRML_MUSTINLINE int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
    int16x8_t v, int16_t c) {
  int16x8_t v_low = _vmulq_n_s16(v, c);
  int16x8_t v_high = _vshrq_n_s16((int32_t)1, _vqdmulhq_n_s16(v, c), int16x8_t);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  return libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant(
      v, c);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c) {
  int16x8_t c0 = _vdupq_n_s16(c);
  v.low = _vandq_s16(v.low, c0);
  v.high = _vandq_s16(v.high, c0);
  return v;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
shift_right_ef(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  v.low = _vshrq_n_s16((int32_t)15, v.low, int16x8_t);
  v.high = _vshrq_n_s16((int32_t)15, v.high, int16x8_t);
  return v;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_to_unsigned_representative(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t = shift_right_ef(a);
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector fm =
      libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_neon_arithmetic_add(a, &fm);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_to_unsigned_representative_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_arithmetic_to_unsigned_representative(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_compress_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t half = _vdupq_n_s16((int16_t)1664);
  int16x8_t quarter = _vdupq_n_s16((int16_t)832);
  int16x8_t shifted = _vsubq_s16(half, v.low);
  int16x8_t mask0 = _vshrq_n_s16((int32_t)15, shifted, int16x8_t);
  int16x8_t shifted_to_positive = _veorq_s16(mask0, shifted);
  int16x8_t shifted_positive_in_range =
      _vsubq_s16(shifted_to_positive, quarter);
  v.low = _vreinterpretq_s16_u16(_vshrq_n_u16(
      (int32_t)15, _vreinterpretq_u16_s16(shifted_positive_in_range),
      uint16x8_t));
  int16x8_t shifted0 = _vsubq_s16(half, v.high);
  int16x8_t mask = _vshrq_n_s16((int32_t)15, shifted0, int16x8_t);
  int16x8_t shifted_to_positive0 = _veorq_s16(mask, shifted0);
  int16x8_t shifted_positive_in_range0 =
      _vsubq_s16(shifted_to_positive0, quarter);
  v.high = _vreinterpretq_s16_u16(_vshrq_n_u16(
      (int32_t)15, _vreinterpretq_u16_s16(shifted_positive_in_range0),
      uint16x8_t));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_1_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return libcrux_ml_kem_vector_neon_compress_compress_1(v);
}

KRML_MUSTINLINE int16_t
libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
    int16_t coefficient_bits) {
  switch (coefficient_bits) {
    case 4: {
      break;
    }
    case 5: {
      return (int16_t)31;
    }
    case 10: {
      return (int16_t)1023;
    }
    case 11: {
      return (int16_t)2047;
    }
    default: {
      int16_t x = coefficient_bits;
      return ((int16_t)1 << (uint32_t)x) - (int16_t)1;
    }
  }
  return (int16_t)15;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_decompress_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector z =
      libcrux_ml_kem_vector_neon_vector_type_ZERO();
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector s =
      libcrux_ml_kem_vector_neon_arithmetic_sub(z, &a);
  return libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
      s, (int16_t)1665);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_decompress_1_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_compress_decompress_1(a);
}

KRML_MUSTINLINE int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
    int16x8_t v, int16x8_t c) {
  int16x8_t v_low = _vmulq_s16(v, c);
  int16x8_t v_high = _vshrq_n_s16((int32_t)1, _vqdmulhq_s16(v, c), int16x8_t);
  return libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
      v_low, v_high);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  Eurydice_arr_e5 zetas = {
      .data = {zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4}};
  int16x8_t zeta =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &zetas, int16_t));
  int16x8_t dup_a = _vreinterpretq_s16_s32(_vtrn1q_s32(
      _vreinterpretq_s32_s16(v.low), _vreinterpretq_s32_s16(v.high)));
  int16x8_t dup_b = _vreinterpretq_s16_s32(_vtrn2q_s32(
      _vreinterpretq_s32_s16(v.low), _vreinterpretq_s32_s16(v.high)));
  int16x8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(dup_b,
                                                                          zeta);
  int16x8_t b = _vsubq_s16(dup_a, t);
  int16x8_t a = _vaddq_s16(dup_a, t);
  v.low = _vreinterpretq_s16_s32(
      _vtrn1q_s32(_vreinterpretq_s32_s16(a), _vreinterpretq_s32_s16(b)));
  v.high = _vreinterpretq_s16_s32(
      _vtrn2q_s32(_vreinterpretq_s32_s16(a), _vreinterpretq_s32_s16(b)));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_1_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(a, zeta1, zeta2, zeta3,
                                                         zeta4);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2) {
  Eurydice_arr_e5 zetas = {
      .data = {zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2}};
  int16x8_t zeta =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &zetas, int16_t));
  int16x8_t dup_a = _vreinterpretq_s16_s64(_vtrn1q_s64(
      _vreinterpretq_s64_s16(v.low), _vreinterpretq_s64_s16(v.high)));
  int16x8_t dup_b = _vreinterpretq_s16_s64(_vtrn2q_s64(
      _vreinterpretq_s64_s16(v.low), _vreinterpretq_s64_s16(v.high)));
  int16x8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(dup_b,
                                                                          zeta);
  int16x8_t b = _vsubq_s16(dup_a, t);
  int16x8_t a = _vaddq_s16(dup_a, t);
  v.low = _vreinterpretq_s16_s64(
      _vtrn1q_s64(_vreinterpretq_s64_s16(a), _vreinterpretq_s64_s16(b)));
  v.high = _vreinterpretq_s16_s64(
      _vtrn2q_s64(_vreinterpretq_s64_s16(a), _vreinterpretq_s64_s16(b)));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_2_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(a, zeta1, zeta2);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta) {
  int16x8_t zeta0 = _vdupq_n_s16(zeta);
  int16x8_t t =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          v.high, zeta0);
  v.high = _vsubq_s16(v.low, t);
  v.low = _vaddq_s16(v.low, t);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_3_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  Eurydice_arr_e5 zetas = {
      .data = {zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4}};
  int16x8_t zeta =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &zetas, int16_t));
  int16x8_t a0 = _vreinterpretq_s16_s32(_vtrn1q_s32(
      _vreinterpretq_s32_s16(v.low), _vreinterpretq_s32_s16(v.high)));
  int16x8_t b0 = _vreinterpretq_s16_s32(_vtrn2q_s32(
      _vreinterpretq_s32_s16(v.low), _vreinterpretq_s32_s16(v.high)));
  int16x8_t b_minus_a = _vsubq_s16(b0, a0);
  int16x8_t a = _vaddq_s16(a0, b0);
  int16x8_t a1 =
      libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(a);
  int16x8_t b =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          b_minus_a, zeta);
  v.low = _vreinterpretq_s16_s32(
      _vtrn1q_s32(_vreinterpretq_s32_s16(a1), _vreinterpretq_s32_s16(b)));
  v.high = _vreinterpretq_s16_s32(
      _vtrn2q_s32(_vreinterpretq_s32_s16(a1), _vreinterpretq_s32_s16(b)));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(a, zeta1, zeta2,
                                                             zeta3, zeta4);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2) {
  Eurydice_arr_e5 zetas = {
      .data = {zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2}};
  int16x8_t zeta =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &zetas, int16_t));
  int16x8_t a0 = _vreinterpretq_s16_s64(_vtrn1q_s64(
      _vreinterpretq_s64_s16(v.low), _vreinterpretq_s64_s16(v.high)));
  int16x8_t b0 = _vreinterpretq_s16_s64(_vtrn2q_s64(
      _vreinterpretq_s64_s16(v.low), _vreinterpretq_s64_s16(v.high)));
  int16x8_t b_minus_a = _vsubq_s16(b0, a0);
  int16x8_t a = _vaddq_s16(a0, b0);
  int16x8_t b =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
          b_minus_a, zeta);
  v.low = _vreinterpretq_s16_s64(
      _vtrn1q_s64(_vreinterpretq_s64_s16(a), _vreinterpretq_s64_s16(b)));
  v.high = _vreinterpretq_s16_s64(
      _vtrn2q_s64(_vreinterpretq_s64_s16(a), _vreinterpretq_s64_s16(b)));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(a, zeta1, zeta2);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta) {
  int16x8_t zeta0 = _vdupq_n_s16(zeta);
  int16x8_t b_minus_a = _vsubq_s16(v.high, v.low);
  v.low = _vaddq_s16(v.low, v.high);
  v.high = libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
      b_minus_a, zeta0);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta) {
  return libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_multiply(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  Eurydice_arr_e5 zetas = {
      .data = {zeta1, zeta3, -zeta1, -zeta3, zeta2, zeta4, -zeta2, -zeta4}};
  int16x8_t zeta =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &zetas, int16_t));
  int16x8_t a0 = _vtrn1q_s16(lhs->low, lhs->high);
  int16x8_t a1 = _vtrn2q_s16(lhs->low, lhs->high);
  int16x8_t b0 = _vtrn1q_s16(rhs->low, rhs->high);
  int16x8_t b1 = _vtrn2q_s16(rhs->low, rhs->high);
  int16x8_t a1b1 =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(a1,
                                                                          b1);
  int32x4_t a1b1_low = _vmull_s16(_vget_low_s16(a1b1), _vget_low_s16(zeta));
  int32x4_t a1b1_high = _vmull_high_s16(a1b1, zeta);
  int16x8_t fst_low = _vreinterpretq_s16_s32(
      _vmlal_s16(a1b1_low, _vget_low_s16(a0), _vget_low_s16(b0)));
  int16x8_t fst_high =
      _vreinterpretq_s16_s32(_vmlal_high_s16(a1b1_high, a0, b0));
  int32x4_t a0b1_low = _vmull_s16(_vget_low_s16(a0), _vget_low_s16(b1));
  int32x4_t a0b1_high = _vmull_high_s16(a0, b1);
  int16x8_t snd_low = _vreinterpretq_s16_s32(
      _vmlal_s16(a0b1_low, _vget_low_s16(a1), _vget_low_s16(b0)));
  int16x8_t snd_high =
      _vreinterpretq_s16_s32(_vmlal_high_s16(a0b1_high, a1, b0));
  int16x8_t fst_low16 = _vtrn1q_s16(fst_low, fst_high);
  int16x8_t fst_high16 = _vtrn2q_s16(fst_low, fst_high);
  int16x8_t snd_low16 = _vtrn1q_s16(snd_low, snd_high);
  int16x8_t snd_high16 = _vtrn2q_s16(snd_low, snd_high);
  int16x8_t fst =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
          fst_low16, fst_high16);
  int16x8_t snd =
      libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
          snd_low16, snd_high16);
  int32x4_t low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(fst, snd));
  int32x4_t high0 = _vreinterpretq_s32_s16(_vtrn2q_s16(fst, snd));
  int16x8_t low1 = _vreinterpretq_s16_s32(_vtrn1q_s32(low0, high0));
  int16x8_t high1 = _vreinterpretq_s16_s32(_vtrn2q_s32(low0, high0));
  Eurydice_arr_88 indexes = {.data = {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 4U, 5U,
                                      6U, 7U, 12U, 13U, 14U, 15U}};
  uint8x16_t index =
      _vld1q_u8(Eurydice_array_to_slice((size_t)16U, &indexes, uint8_t));
  int16x8_t low2 =
      _vreinterpretq_s16_u8(_vqtbl1q_u8(_vreinterpretq_u8_s16(low1), index));
  int16x8_t high2 =
      _vreinterpretq_s16_u8(_vqtbl1q_u8(_vreinterpretq_u8_s16(high1), index));
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = low2, .high = high2});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_multiply_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4) {
  return libcrux_ml_kem_vector_neon_ntt_ntt_multiply(lhs, rhs, zeta1, zeta2,
                                                     zeta3, zeta4);
}

KRML_MUSTINLINE Eurydice_arr_8b
libcrux_ml_kem_vector_neon_serialize_serialize_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  Eurydice_arr_e5 shifter = {.data = {(int16_t)0, (int16_t)1, (int16_t)2,
                                      (int16_t)3, (int16_t)4, (int16_t)5,
                                      (int16_t)6, (int16_t)7}};
  int16x8_t shift =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &shifter, int16_t));
  int16x8_t low0 = _vshlq_s16(v.low, shift);
  int16x8_t high0 = _vshlq_s16(v.high, shift);
  int16_t low = _vaddvq_s16(low0);
  int16_t high = _vaddvq_s16(high0);
  return (
      KRML_CLITERAL(Eurydice_arr_8b){.data = {(uint8_t)low, (uint8_t)high}});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_8b libcrux_ml_kem_vector_neon_serialize_1_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_1(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_1(Eurydice_slice a) {
  int16x8_t one = _vdupq_n_s16((int16_t)1);
  int16x8_t low0 = _vdupq_n_s16(
      (int16_t)Eurydice_slice_index(a, (size_t)0U, uint8_t, uint8_t *));
  int16x8_t high0 = _vdupq_n_s16(
      (int16_t)Eurydice_slice_index(a, (size_t)1U, uint8_t, uint8_t *));
  Eurydice_arr_e5 shifter = {.data = {(int16_t)0, (int16_t)255, (int16_t)-2,
                                      (int16_t)-3, (int16_t)-4, (int16_t)-5,
                                      (int16_t)-6, (int16_t)-7}};
  int16x8_t shift =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &shifter, int16_t));
  int16x8_t low = _vshlq_s16(low0, shift);
  int16x8_t high = _vshlq_s16(high0, shift);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vandq_s16(low, one), .high = _vandq_s16(high, one)});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_1_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_1(a);
}

KRML_MUSTINLINE Eurydice_arr_c4
libcrux_ml_kem_vector_neon_serialize_serialize_4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  Eurydice_arr_e5 shifter = {.data = {(int16_t)0, (int16_t)4, (int16_t)8,
                                      (int16_t)12, (int16_t)0, (int16_t)4,
                                      (int16_t)8, (int16_t)12}};
  int16x8_t shift =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &shifter, int16_t));
  uint16x8_t lowt = _vshlq_u16(_vreinterpretq_u16_s16(v.low), shift);
  uint16x8_t hight = _vshlq_u16(_vreinterpretq_u16_s16(v.high), shift);
  uint64_t sum0 = (uint64_t)_vaddv_u16(_vget_low_u16(lowt));
  uint64_t sum1 = (uint64_t)_vaddv_u16(_vget_high_u16(lowt));
  uint64_t sum2 = (uint64_t)_vaddv_u16(_vget_low_u16(hight));
  uint64_t sum3 = (uint64_t)_vaddv_u16(_vget_high_u16(hight));
  uint64_t sum = ((sum0 | sum1 << 16U) | sum2 << 32U) | sum3 << 48U;
  return core_num__u64__to_le_bytes(sum);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_c4 libcrux_ml_kem_vector_neon_serialize_4_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_4(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_4(Eurydice_slice v) {
  Eurydice_arr_e2 input = libcrux_ml_kem_vector_portable_deserialize_4_b8(v);
  Eurydice_arr_e2 input_i16s =
      libcrux_ml_kem_vector_portable_to_i16_array_b8(input);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_s16(Eurydice_array_to_subslice3(&input_i16s, (size_t)0U,
                                                    (size_t)8U, int16_t *)),
      .high = _vld1q_s16(Eurydice_array_to_subslice3(&input_i16s, (size_t)8U,
                                                     (size_t)16U, int16_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_4_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_4(a);
}

KRML_MUSTINLINE Eurydice_arr_77
libcrux_ml_kem_vector_neon_serialize_serialize_5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  Eurydice_arr_e2 out_i16s =
      libcrux_ml_kem_vector_neon_vector_type_to_i16_array(v);
  Eurydice_arr_e2 out = libcrux_ml_kem_vector_portable_from_i16_array_b8(
      Eurydice_array_to_slice((size_t)16U, &out_i16s, int16_t));
  return libcrux_ml_kem_vector_portable_serialize_5_b8(out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_77 libcrux_ml_kem_vector_neon_serialize_5_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_5(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_5(Eurydice_slice v) {
  Eurydice_arr_e2 output = libcrux_ml_kem_vector_portable_deserialize_5_b8(v);
  Eurydice_arr_e2 array =
      libcrux_ml_kem_vector_portable_to_i16_array_b8(output);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)0U,
                                                    (size_t)8U, int16_t *)),
      .high = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)8U,
                                                     (size_t)16U, int16_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_5_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_5(a);
}

KRML_MUSTINLINE Eurydice_arr_dc
libcrux_ml_kem_vector_neon_serialize_serialize_10(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int32x4_t low00 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low));
  int32x4_t low10 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low));
  int32x4_t mixt = _vsliq_n_s32((int32_t)10, low00, low10, int32x4_t);
  int64x2_t low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt));
  int64x2_t low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt));
  int64x2_t low_mix = _vsliq_n_s64((int32_t)20, low0, low1, int64x2_t);
  int32x4_t high00 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high));
  int32x4_t high10 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high));
  int32x4_t mixt0 = _vsliq_n_s32((int32_t)10, high00, high10, int32x4_t);
  int64x2_t high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt0, mixt0));
  int64x2_t high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt0, mixt0));
  int64x2_t high_mix = _vsliq_n_s64((int32_t)20, high0, high1, int64x2_t);
  Eurydice_arr_60 result32 = {.data = {0U}};
  _vst1q_u8(Eurydice_array_to_subslice3(&result32, (size_t)0U, (size_t)16U,
                                        uint8_t *),
            _vreinterpretq_u8_s64(low_mix));
  _vst1q_u8(Eurydice_array_to_subslice3(&result32, (size_t)16U, (size_t)32U,
                                        uint8_t *),
            _vreinterpretq_u8_s64(high_mix));
  Eurydice_arr_dc result = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)0U, (size_t)5U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)0U, (size_t)5U, uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)5U, (size_t)10U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)8U, (size_t)13U,
                                  uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)10U, (size_t)15U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)16U, (size_t)21U,
                                  uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)15U, (size_t)20U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)24U, (size_t)29U,
                                  uint8_t *),
      uint8_t);
  return result;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_dc libcrux_ml_kem_vector_neon_serialize_10_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_10(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_10(Eurydice_slice v) {
  Eurydice_arr_e2 output = libcrux_ml_kem_vector_portable_deserialize_10_b8(v);
  Eurydice_arr_e2 array =
      libcrux_ml_kem_vector_portable_to_i16_array_b8(output);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)0U,
                                                    (size_t)8U, int16_t *)),
      .high = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)8U,
                                                     (size_t)16U, int16_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_10_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_10(a);
}

KRML_MUSTINLINE Eurydice_arr_f3
libcrux_ml_kem_vector_neon_serialize_serialize_11(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  Eurydice_arr_e2 out_i16s =
      libcrux_ml_kem_vector_neon_vector_type_to_i16_array(v);
  Eurydice_arr_e2 out = libcrux_ml_kem_vector_portable_from_i16_array_b8(
      Eurydice_array_to_slice((size_t)16U, &out_i16s, int16_t));
  return libcrux_ml_kem_vector_portable_serialize_11_b8(out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_f3 libcrux_ml_kem_vector_neon_serialize_11_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_11(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_11(Eurydice_slice v) {
  Eurydice_arr_e2 output = libcrux_ml_kem_vector_portable_deserialize_11_b8(v);
  Eurydice_arr_e2 array =
      libcrux_ml_kem_vector_portable_to_i16_array_b8(output);
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)0U,
                                                    (size_t)8U, int16_t *)),
      .high = _vld1q_s16(Eurydice_array_to_subslice3(&array, (size_t)8U,
                                                     (size_t)16U, int16_t *))});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_11_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_11(a);
}

KRML_MUSTINLINE Eurydice_arr_6d
libcrux_ml_kem_vector_neon_serialize_serialize_12(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int32x4_t low00 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low));
  int32x4_t low10 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low));
  int32x4_t mixt = _vsliq_n_s32((int32_t)12, low00, low10, int32x4_t);
  int64x2_t low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt));
  int64x2_t low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt));
  int64x2_t low_mix = _vsliq_n_s64((int32_t)24, low0, low1, int64x2_t);
  int32x4_t high00 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high));
  int32x4_t high10 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high));
  int32x4_t mixt0 = _vsliq_n_s32((int32_t)12, high00, high10, int32x4_t);
  int64x2_t high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt0, mixt0));
  int64x2_t high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt0, mixt0));
  int64x2_t high_mix = _vsliq_n_s64((int32_t)24, high0, high1, int64x2_t);
  Eurydice_arr_60 result32 = {.data = {0U}};
  _vst1q_u8(Eurydice_array_to_subslice3(&result32, (size_t)0U, (size_t)16U,
                                        uint8_t *),
            _vreinterpretq_u8_s64(low_mix));
  _vst1q_u8(Eurydice_array_to_subslice3(&result32, (size_t)16U, (size_t)32U,
                                        uint8_t *),
            _vreinterpretq_u8_s64(high_mix));
  Eurydice_arr_6d result = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)0U, (size_t)6U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)0U, (size_t)6U, uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)6U, (size_t)12U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)8U, (size_t)14U,
                                  uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)12U, (size_t)18U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)16U, (size_t)22U,
                                  uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&result, (size_t)18U, (size_t)24U, uint8_t *),
      Eurydice_array_to_subslice3(&result32, (size_t)24U, (size_t)30U,
                                  uint8_t *),
      uint8_t);
  return result;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_6d libcrux_ml_kem_vector_neon_serialize_12_61(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_serialize_serialize_12(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_12(Eurydice_slice v) {
  Eurydice_arr_88 indexes = {.data = {0U, 1U, 1U, 2U, 3U, 4U, 4U, 5U, 6U, 7U,
                                      7U, 8U, 9U, 10U, 10U, 11U}};
  uint8x16_t index_vec =
      _vld1q_u8(Eurydice_array_to_slice((size_t)16U, &indexes, uint8_t));
  Eurydice_arr_e5 shifts = {.data = {(int16_t)0, (int16_t)-4, (int16_t)0,
                                     (int16_t)-4, (int16_t)0, (int16_t)-4,
                                     (int16_t)0, (int16_t)-4}};
  int16x8_t shift_vec =
      _vld1q_s16(Eurydice_array_to_slice((size_t)8U, &shifts, int16_t));
  uint16x8_t mask12 = _vdupq_n_u16(4095U);
  Eurydice_arr_88 input0 = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&input0, (size_t)0U, (size_t)12U, uint8_t *),
      Eurydice_slice_subslice3(v, (size_t)0U, (size_t)12U, uint8_t *), uint8_t);
  uint8x16_t input_vec0 =
      _vld1q_u8(Eurydice_array_to_slice((size_t)16U, &input0, uint8_t));
  Eurydice_arr_88 input1 = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&input1, (size_t)0U, (size_t)12U, uint8_t *),
      Eurydice_slice_subslice3(v, (size_t)12U, (size_t)24U, uint8_t *),
      uint8_t);
  uint8x16_t input_vec1 =
      _vld1q_u8(Eurydice_array_to_slice((size_t)16U, &input1, uint8_t));
  uint16x8_t moved0 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec0, index_vec));
  uint16x8_t shifted0 = _vshlq_u16(moved0, shift_vec);
  int16x8_t low = _vreinterpretq_s16_u16(_vandq_u16(shifted0, mask12));
  uint16x8_t moved1 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec1, index_vec));
  uint16x8_t shifted1 = _vshlq_u16(moved1, shift_vec);
  int16x8_t high = _vreinterpretq_s16_u16(_vandq_u16(shifted1, mask12));
  return (KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector){
      .low = low, .high = high});
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_12_61(Eurydice_slice a) {
  return libcrux_ml_kem_vector_neon_serialize_deserialize_12(a);
}

KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_neon_rej_sample(Eurydice_slice a, Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          core_slice___Slice_T___chunks(a, (size_t)3U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, Eurydice_slice, core_slice_iter_Chunks);
  while (true) {
    core_option_Option_1b uu____0 =
        core_slice_iter__core__iter__traits__iterator__Iterator___a___Slice_T____for_core__slice__iter__Chunks__a__T__TraitClause_0___next(
            &iter, uint8_t, core_option_Option_1b);
    if (uu____0.tag == core_option_None) {
      break;
    } else {
      Eurydice_slice bytes = uu____0.f0;
      int16_t b1 =
          (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
      int16_t b2 =
          (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
      int16_t b3 =
          (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
      int16_t d1 = (b2 & (int16_t)15) << 8U | b1;
      int16_t d2 = b3 << 4U | b2 >> 4U;
      if (d1 < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
        if (sampled < (size_t)16U) {
          Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d1;
          sampled++;
        }
      }
      if (d2 < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
        if (sampled < (size_t)16U) {
          Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d2;
          sampled++;
        }
      }
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
size_t libcrux_ml_kem_vector_neon_rej_sample_61(Eurydice_slice a,
                                                Eurydice_slice out) {
  return libcrux_ml_kem_vector_neon_rej_sample(a, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
inline libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_clone_74(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static Eurydice_arr_f9 ZERO_d6_c5(void) {
  Eurydice_arr_f9 lit;
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_neon_ZERO_61(););
  memcpy(lit.data, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector));
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
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_to_reduced_ring_element_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_12_61(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_cond_subtract_3329_61(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_e3(
    Eurydice_slice public_key, Eurydice_arr_f30 *deserialized_pk) {
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
    Eurydice_arr_f9 uu____0 =
        deserialize_to_reduced_ring_element_c5(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_fd(Eurydice_arr_340 *input) {
  Eurydice_arr_fe uu____0 = libcrux_sha3_neon_x2_incremental_init();
  Eurydice_arr_54 state = {
      .data = {uu____0, libcrux_sha3_neon_x2_incremental_init()}};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state.data, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final_2d with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_2d_fd(Eurydice_arr_340 *input) {
  return shake128_init_absorb_final_fd(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_45
shake128_squeeze_first_three_blocks_fd(Eurydice_arr_54 *st) {
  Eurydice_arr_45 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out2);
  Eurydice_arr_b0 out3 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out3);
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->data, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks_2d with
const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_45
shake128_squeeze_first_three_blocks_2d_fd(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_37(
    Eurydice_arr_45 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_a9
shake128_squeeze_next_block_fd(Eurydice_arr_54 *st) {
  Eurydice_arr_a9 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out2);
  Eurydice_arr_27 out3 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out3);
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->data, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block_2d with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_a9
shake128_squeeze_next_block_2d_fd(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_370(
    Eurydice_arr_a9 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static Eurydice_arr_f9 ZERO_c5(void) {
  Eurydice_arr_f9 lit;
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_neon_ZERO_61(););
  memcpy(lit.data, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9 from_i16_array_c5(Eurydice_slice a) {
  Eurydice_arr_f9 result = ZERO_c5();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    result.data[i0] =
        libcrux_ml_kem_vector_neon_from_i16_array_61(Eurydice_slice_subslice3(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9 from_i16_array_d6_c5(Eurydice_slice a) {
  return from_i16_array_c5(a);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static Eurydice_arr_f9 call_mut_e7_cd1(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_f30
sample_from_xof_cd1(Eurydice_arr_340 *seeds) {
  Eurydice_arr_fb sampled_coefficients = {.data = {0U}};
  Eurydice_arr_04 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_54 xof_state = shake128_init_absorb_final_2d_fd(seeds);
  Eurydice_arr_45 randomness0 =
      shake128_squeeze_first_three_blocks_2d_fd(&xof_state);
  bool done = sample_from_uniform_distribution_next_37(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a9 randomness =
          shake128_squeeze_next_block_2d_fd(&xof_state);
      done = sample_from_uniform_distribution_next_370(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_f30 arr_mapped_str;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_cd1(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_cd1(Eurydice_arr_e21 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_340 seeds; Eurydice_arr_480 repeat_expression[2U];
      KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)2U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_f30 sampled = sample_from_xof_cd1(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)2U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_2d
with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_2d_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_H(input);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash,
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e1(
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_e3(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 =
      libcrux_ml_kem_utils_into_padded_array_9e(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_e21 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue =
      libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  sample_matrix_A_cd1(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_2d_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
to_unsigned_field_modulus_c5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a) {
  return libcrux_ml_kem_vector_neon_to_unsigned_representative_61(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_cc
serialize_uncompressed_ring_element_c5(Eurydice_arr_f9 *re) {
  Eurydice_arr_cc serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        to_unsigned_field_modulus_c5(re->data[i0]);
    Eurydice_arr_6d bytes =
        libcrux_ml_kem_vector_neon_serialize_12_61(coefficient);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void serialize_vector_e3(Eurydice_arr_f30 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, key, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_c5(&re);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_mut_37(
    Eurydice_arr_f30 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_30 *serialized) {
  serialize_vector_e3(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_37(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *self,
    Eurydice_arr_30 *serialized) {
  serialize_public_key_mut_37(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_37(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self,
    Eurydice_arr_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_37(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE Eurydice_arr_30
serialize_public_key_37(Eurydice_arr_f30 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_30 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_37(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE Eurydice_arr_30 serialized_dd_37(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *self) {
  return libcrux_ml_kem_types_from_fd_4d(serialize_public_key_37(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_30 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_37(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self) {
  return serialized_dd_37(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair512
serialize_unpacked_secret_key_4c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d *public_key,
    Eurydice_arr_f30 *private_key) {
  Eurydice_arr_30 public_key_serialized = serialize_public_key_37(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_56 secret_key_serialized = {.data = {0U}};
  serialize_vector_e3(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_90(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self,
    Eurydice_arr_7f0 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      serialize_unpacked_secret_key_4c(&self->public_key.ind_cpa_public_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_7f0 libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_90(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self) {
  Eurydice_arr_7f0 sk = libcrux_ml_kem_types_default_d3_2a();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_90(self, &sk);
  return sk;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_to_uncompressed_ring_element_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_deserialize_12_61(bytes);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_vector_e3(
    Eurydice_slice secret_key, Eurydice_arr_f30 *secret_as_ntt) {
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          deserialize_to_uncompressed_ring_element_c5(Eurydice_slice_subslice3(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static Eurydice_arr_f9 call_mut_e7_561(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_f30
sample_from_xof_561(Eurydice_arr_340 *seeds) {
  Eurydice_arr_fb sampled_coefficients = {.data = {0U}};
  Eurydice_arr_04 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_73 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
          seeds);
  Eurydice_arr_45 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_37(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a9 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
              &xof_state);
      done = sample_from_uniform_distribution_next_370(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_f30 arr_mapped_str;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_561(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_561(Eurydice_arr_e21 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_340 seeds; Eurydice_arr_480 repeat_expression[2U];
      KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)2U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_f30 sampled = sample_from_xof_561(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)2U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_441(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_e3(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_e21 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_561(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_c2(
    Eurydice_arr_7f0 *private_key,
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_e3(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_441(ind_cpa_public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static Eurydice_arr_f30 default_70_e3(void) {
  Eurydice_arr_f30 lit;
  Eurydice_arr_f9 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_c5(););
  memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_f9));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d default_8b_e3(
    void) {
  Eurydice_arr_f30 uu____0;
  Eurydice_arr_f9 repeat_expression0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_c5(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)2U * sizeof(Eurydice_arr_f9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_f30 repeat_expression1[2U];
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, Eurydice_arr_f30 lit;
      Eurydice_arr_f9 repeat_expression[2U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_c5(););
      memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_f9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1,
         (size_t)2U * sizeof(Eurydice_arr_f30));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
libcrux_ml_kem_ind_cca_unpacked_default_30_e3(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d){
          .ind_cpa_public_key = default_8b_e3(),
          .public_key_hash = {.data = {0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_e3(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_7d uu____0 = {
      .ind_cpa_private_key = default_70_e3(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_e3()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_2d
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_2d_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_48(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)2U;
  return G_2d_fd(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_49(Eurydice_arr_cf *input) {
  Eurydice_arr_a80 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_f2 out0 = {.data = {0U}};
  Eurydice_arr_f2 out1 = {.data = {0U}};
  Eurydice_arr_f2 out2 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out2);
  Eurydice_arr_f2 out3 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out3);
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)192U, &out1, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_2d
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_2d_49(Eurydice_arr_cf *input) {
  return PRFxN_49(input);
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
static KRML_MUSTINLINE Eurydice_arr_f9
sample_from_binomial_distribution_2_c5(Eurydice_slice randomness) {
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
  return from_i16_array_d6_c5(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
sample_from_binomial_distribution_3_c5(Eurydice_slice randomness) {
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
  return from_i16_array_d6_c5(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE Eurydice_arr_f9
sample_from_binomial_distribution_a5(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_c5(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_c5(Eurydice_arr_f9 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t =
        libcrux_ml_kem_vector_neon_multiply_by_constant_61(re->data[j + step],
                                                           (int16_t)-1600);
    re->data[j + step] = libcrux_ml_kem_vector_neon_sub_61(re->data[j], &t);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____1 =
        libcrux_ml_kem_vector_neon_add_61(re->data[j], &t);
    re->data[j] = uu____1;
  }
}

typedef struct libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2_s {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector fst;
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector snd;
} libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2;

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2
ntt_layer_int_vec_step_c5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector b, int16_t zeta_r) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector t =
      libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(b, zeta_r);
  b = libcrux_ml_kem_vector_neon_sub_61(a, &t);
  a = libcrux_ml_kem_vector_neon_add_61(a, &t);
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2){
          .fst = a, .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_c5(size_t *zeta_i,
                                                   Eurydice_arr_f9 *re,
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
          ntt_layer_int_vec_step_c5(re->data[j], re->data[j + step_vec],
                                    libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x = uu____0.fst;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_c5(size_t *zeta_i,
                                              Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_ntt_layer_3_step_61(
              re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->data[round] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_c5(size_t *zeta_i,
                                              Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_neon_ntt_layer_2_step_61(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_c5(size_t *zeta_i,
                                              Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_neon_ntt_layer_1_step_61(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)2U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)3U));
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_c5(Eurydice_arr_f9 *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_barrett_reduce_61(myself->data[i0]);
    myself->data[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_d6_c5(Eurydice_arr_f9 *self) {
  poly_barrett_reduce_c5(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_c5(
    Eurydice_arr_f9 *re) {
  ntt_at_layer_7_c5(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_c5(&zeta_i, re);
  ntt_at_layer_2_c5(&zeta_i, re);
  ntt_at_layer_1_c5(&zeta_i, re);
  poly_barrett_reduce_d6_c5(re);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_1f1(
    Eurydice_arr_f30 *re_as_ntt, Eurydice_arr_3e *prf_input,
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
  Eurydice_arr_a80 prf_outputs = PRFxN_2d_49(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_a5(Eurydice_array_to_slice(
              (size_t)192U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_c5(&re_as_ntt->data[i0]););
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static Eurydice_arr_f9 call_mut_73_c21(void **_) { return ZERO_d6_c5(); }

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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9 ntt_multiply_c5(Eurydice_arr_f9 *myself,
                                                       Eurydice_arr_f9 *rhs) {
  Eurydice_arr_f9 out = ZERO_c5();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_ntt_multiply_61(
            &myself->data[i0], &rhs->data[i0],
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)1U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)2U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)3U));
    out.data[i0] = uu____0;
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
ntt_multiply_d6_c5(Eurydice_arr_f9 *self, Eurydice_arr_f9 *rhs) {
  return ntt_multiply_c5(self, rhs);
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_e3(Eurydice_arr_f9 *myself,
                                                   Eurydice_arr_f9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_61(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_e3(Eurydice_arr_f9 *self,
                                                      Eurydice_arr_f9 *rhs) {
  add_to_ring_element_e3(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
to_standard_domain_c5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector vector) {
  return libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
      vector,
      LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_c5(
    Eurydice_arr_f9 *myself, Eurydice_arr_f9 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form = to_standard_domain_c5(myself->data[j]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector sum =
        libcrux_ml_kem_vector_neon_add_61(coefficient_normal_form,
                                          &error->data[j]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector red =
        libcrux_ml_kem_vector_neon_barrett_reduce_61(sum);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_d6_c5(
    Eurydice_arr_f9 *self, Eurydice_arr_f9 *error) {
  add_standard_error_reduce_c5(self, error);
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
static KRML_MUSTINLINE void compute_As_plus_e_e3(
    Eurydice_arr_f30 *t_as_ntt, Eurydice_arr_e21 *matrix_A,
    Eurydice_arr_f30 *s_as_ntt, Eurydice_arr_f30 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, matrix_A, Eurydice_arr_f30),
               Eurydice_arr_f30);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f30 *row = &matrix_A->data[i0];
    Eurydice_arr_f9 uu____0 = ZERO_d6_c5();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_f9),
                  Eurydice_arr_f9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_f9 *matrix_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_e3(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_c5(&t_as_ntt->data[i0],
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_c21(
    Eurydice_slice key_generation_seed, Eurydice_arr_f30 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_48(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_e21 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_cd1(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_1f1(private_key, &prf_input, 0U);
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_c21(&lvalue););
  Eurydice_arr_f30 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_1f1(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_e3(&public_key->t_as_ntt, &public_key->A, private_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
*/
static Eurydice_arr_f9 call_mut_b4_e3(void **_) { return ZERO_d6_c5(); }

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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
*/
static Eurydice_arr_f30 call_mut_7b_e3(void **_) {
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_e3(&lvalue););
  return arr_struct;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_c1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static inline Eurydice_arr_f9 clone_c1_c5(Eurydice_arr_f9 *self) {
  return core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)16U, self, libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
      Eurydice_arr_f9);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static Eurydice_arr_e21 transpose_a_e3(Eurydice_arr_e21 ind_cpa_a) {
  Eurydice_arr_e21 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_e3(&lvalue););
  Eurydice_arr_e21 A = arr_struct;
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          Eurydice_arr_f9 uu____0 = clone_c1_c5(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_581(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_c21(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_e21 A = transpose_a_e3(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_30 pk_serialized = serialize_public_key_37(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_2d_fd(Eurydice_array_to_slice((size_t)800U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_48(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_2d_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$2size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector

*/
typedef struct tuple_710_s {
  Eurydice_arr_f30 fst;
  Eurydice_arr_f9 snd;
} tuple_710;

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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_f1_d51(void **_) { return ZERO_d6_c5(); }

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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_dd_d51(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_490(Eurydice_arr_cf *input) {
  Eurydice_arr_a01 out = {.data = {{.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out2);
  Eurydice_arr_d1 out3 = {.data = {0U}};
  KRML_MAYBE_UNUSED_VAR(out3);
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_2d
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_2d_490(Eurydice_arr_cf *input) {
  return PRFxN_490(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE Eurydice_arr_f9
sample_from_binomial_distribution_e3(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_c5(randomness);
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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_1f1(
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_f30 *error_1) {
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
  Eurydice_arr_a01 prf_outputs = PRFxN_2d_490(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          sample_from_binomial_distribution_e3(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_a6(Eurydice_slice input) {
  Eurydice_arr_d1 digest = {.data = {0U}};
  Eurydice_arr_d1 dummy = {.data = {0U}};
  libcrux_sha3_neon_x2_shake256(
      input, input, Eurydice_array_to_slice((size_t)128U, &digest, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &dummy, uint8_t));
  return digest;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_2d_490(Eurydice_slice input) {
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static Eurydice_arr_f9 call_mut_a8_e3(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_c5(size_t *zeta_i,
                                                     Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_61(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)2U),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)3U));
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_c5(size_t *zeta_i,
                                                     Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_61(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_c5(size_t *zeta_i,
                                                     Eurydice_arr_f9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_61(
              re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->data[round] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2
inv_ntt_layer_int_vec_step_reduce_c5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector b, int16_t zeta_r) {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a_minus_b =
      libcrux_ml_kem_vector_neon_sub_61(b, &a);
  a = libcrux_ml_kem_vector_neon_barrett_reduce_61(
      libcrux_ml_kem_vector_neon_add_61(a, &b));
  b = libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(a_minus_b,
                                                                    zeta_r);
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_x2){
          .fst = a, .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_c5(size_t *zeta_i,
                                                          Eurydice_arr_f9 *re,
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
          inv_ntt_layer_int_vec_step_reduce_c5(
              re->data[j], re->data[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x = uu____0.fst;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_e3(Eurydice_arr_f9 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_c5(&zeta_i, re);
  invert_ntt_at_layer_2_c5(&zeta_i, re);
  invert_ntt_at_layer_3_c5(&zeta_i, re);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_c5(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_c5(Eurydice_arr_f9 *myself,
                                                Eurydice_arr_f9 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
                myself->data[j], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector sum =
        libcrux_ml_kem_vector_neon_add_61(coefficient_normal_form,
                                          &error->data[j]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector red =
        libcrux_ml_kem_vector_neon_barrett_reduce_61(sum);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_d6_c5(Eurydice_arr_f9 *self,
                                                   Eurydice_arr_f9 *error) {
  add_error_reduce_c5(self, error);
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
static KRML_MUSTINLINE Eurydice_arr_f30
compute_vector_u_e3(Eurydice_arr_e21 *a_as_ntt, Eurydice_arr_f30 *r_as_ntt,
                    Eurydice_arr_f30 *error_1) {
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_e3(&lvalue););
  Eurydice_arr_f30 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)2U, a_as_ntt, Eurydice_arr_f30),
                Eurydice_arr_f30);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_f30 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_f9),
                 Eurydice_arr_f9);
         i++) {
      size_t j = i;
      Eurydice_arr_f9 *a_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_e3(&result.data[i1], &product);
    }
    invert_ntt_montgomery_e3(&result.data[i1]);
    add_error_reduce_d6_c5(&result.data[i1], &error_1->data[i1]);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE uint32x4_t compress_int32x4_t_ef(uint32x4_t v) {
  uint32x4_t half = _vdupq_n_u32(1664U);
  uint32x4_t compressed = _vshlq_n_u32((int32_t)10, v, uint32x4_t);
  uint32x4_t compressed0 = _vaddq_u32(compressed, half);
  uint32x4_t compressed1 = _vreinterpretq_u32_s32(
      _vqdmulhq_n_s32(_vreinterpretq_s32_u32(compressed0), (int32_t)10321340));
  return _vshrq_n_u32((int32_t)4, compressed1, uint32x4_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_ef(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t mask = _vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)10));
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = compress_int32x4_t_ef(low00);
  uint32x4_t low1 = compress_int32x4_t_ef(low10);
  uint32x4_t high0 = compress_int32x4_t_ef(high00);
  uint32x4_t high1 = compress_int32x4_t_ef(high10);
  int16x8_t low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  int16x8_t high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  v.low = _vandq_s16(low, mask);
  v.high = _vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_61
with const generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_61_ef(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_ef(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_10_3d(Eurydice_arr_f9 *re) {
  Eurydice_arr_b7 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_61_ef(to_unsigned_field_modulus_c5(re->data[i0]));
    Eurydice_arr_dc bytes =
        libcrux_ml_kem_vector_neon_serialize_10_61(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)20U * i0,
                                    (size_t)20U * i0 + (size_t)20U, uint8_t *),
        Eurydice_array_to_slice((size_t)20U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE uint32x4_t compress_int32x4_t_c4(uint32x4_t v) {
  uint32x4_t half = _vdupq_n_u32(1664U);
  uint32x4_t compressed = _vshlq_n_u32((int32_t)11, v, uint32x4_t);
  uint32x4_t compressed0 = _vaddq_u32(compressed, half);
  uint32x4_t compressed1 = _vreinterpretq_u32_s32(
      _vqdmulhq_n_s32(_vreinterpretq_s32_u32(compressed0), (int32_t)10321340));
  return _vshrq_n_u32((int32_t)4, compressed1, uint32x4_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_c4(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t mask = _vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)11));
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = compress_int32x4_t_c4(low00);
  uint32x4_t low1 = compress_int32x4_t_c4(low10);
  uint32x4_t high0 = compress_int32x4_t_c4(high00);
  uint32x4_t high1 = compress_int32x4_t_c4(high10);
  int16x8_t low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  int16x8_t high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  v.low = _vandq_s16(low, mask);
  v.high = _vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_61
with const generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_61_c4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_c4(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_ring_element_u_53(Eurydice_arr_f9 *re) {
  return compress_then_serialize_10_3d(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_90(Eurydice_arr_f30 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, &input, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_53(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_710 encrypt_c1_d51(Eurydice_slice randomness,
                                                Eurydice_arr_e21 *matrix,
                                                Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_f30 arr_struct0;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_d51(&lvalue););
  Eurydice_arr_f30 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_1f1(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_d51(&lvalue););
  Eurydice_arr_f30 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_1f1(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_2d_490(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_f9 error_2 = sample_from_binomial_distribution_e3(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_f30 u = compute_vector_u_e3(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_90(u, ciphertext);
  return (KRML_CLITERAL(tuple_710){.fst = r_as_ntt, .snd = error_2});
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_message_c5(Eurydice_arr_60 *serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
          coefficient_compressed = libcrux_ml_kem_vector_neon_deserialize_1_61(
              Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t *));
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
          libcrux_ml_kem_vector_neon_decompress_1_61(coefficient_compressed);
      re.data[i0] = uu____0;);
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9 add_message_error_reduce_c5(
    Eurydice_arr_f9 *myself, Eurydice_arr_f9 *message, Eurydice_arr_f9 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
                result.data[i0], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector sum1 =
        libcrux_ml_kem_vector_neon_add_61(myself->data[i0], &message->data[i0]);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector sum2 =
        libcrux_ml_kem_vector_neon_add_61(coefficient_normal_form, &sum1);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector red =
        libcrux_ml_kem_vector_neon_barrett_reduce_61(sum2);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9 add_message_error_reduce_d6_c5(
    Eurydice_arr_f9 *self, Eurydice_arr_f9 *message, Eurydice_arr_f9 result) {
  return add_message_error_reduce_c5(self, message, result);
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
static KRML_MUSTINLINE Eurydice_arr_f9 compute_ring_element_v_e3(
    Eurydice_arr_f30 *t_as_ntt, Eurydice_arr_f30 *r_as_ntt,
    Eurydice_arr_f9 *error_2, Eurydice_arr_f9 *message) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_e3(&result, &product););
  invert_ntt_montgomery_e3(&result);
  return add_message_error_reduce_d6_c5(error_2, message, result);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE uint32x4_t compress_int32x4_t_d1(uint32x4_t v) {
  uint32x4_t half = _vdupq_n_u32(1664U);
  uint32x4_t compressed = _vshlq_n_u32((int32_t)4, v, uint32x4_t);
  uint32x4_t compressed0 = _vaddq_u32(compressed, half);
  uint32x4_t compressed1 = _vreinterpretq_u32_s32(
      _vqdmulhq_n_s32(_vreinterpretq_s32_u32(compressed0), (int32_t)10321340));
  return _vshrq_n_u32((int32_t)4, compressed1, uint32x4_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_d1(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t mask = _vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)4));
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = compress_int32x4_t_d1(low00);
  uint32x4_t low1 = compress_int32x4_t_d1(low10);
  uint32x4_t high0 = compress_int32x4_t_d1(high00);
  uint32x4_t high1 = compress_int32x4_t_d1(high10);
  int16x8_t low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  int16x8_t high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  v.low = _vandq_s16(low, mask);
  v.high = _vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_61
with const generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_61_d1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_d1(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_c5(
    Eurydice_arr_f9 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_61_d1(to_unsigned_field_modulus_c5(re.data[i0]));
    Eurydice_arr_c4 bytes =
        libcrux_ml_kem_vector_neon_serialize_4_61(coefficient);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *),
        Eurydice_array_to_slice((size_t)8U, &bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress_int32x4_t
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE uint32x4_t compress_int32x4_t_f4(uint32x4_t v) {
  uint32x4_t half = _vdupq_n_u32(1664U);
  uint32x4_t compressed = _vshlq_n_u32((int32_t)5, v, uint32x4_t);
  uint32x4_t compressed0 = _vaddq_u32(compressed, half);
  uint32x4_t compressed1 = _vreinterpretq_u32_s32(
      _vqdmulhq_n_s32(_vreinterpretq_s32_u32(compressed0), (int32_t)10321340));
  return _vshrq_n_u32((int32_t)4, compressed1, uint32x4_t);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
compress_f4(libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  int16x8_t mask = _vdupq_n_s16(
      libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
          (int16_t)(int32_t)5));
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = compress_int32x4_t_f4(low00);
  uint32x4_t low1 = compress_int32x4_t_f4(low10);
  uint32x4_t high0 = compress_int32x4_t_f4(high00);
  uint32x4_t high1 = compress_int32x4_t_f4(high10);
  int16x8_t low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  int16x8_t high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  v.low = _vandq_s16(low, mask);
  v.high = _vandq_s16(high, mask);
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.neon.compress_61
with const generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector compress_61_f4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return compress_f4(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_c5(
    Eurydice_arr_f9 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficients =
        compress_61_f4(libcrux_ml_kem_vector_neon_to_unsigned_representative_61(
            re.data[i0]));
    Eurydice_arr_77 bytes =
        libcrux_ml_kem_vector_neon_serialize_5_61(coefficients);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t *),
        Eurydice_array_to_slice((size_t)10U, &bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_4c(
    Eurydice_arr_f9 re, Eurydice_slice out) {
  compress_then_serialize_4_c5(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_4c(Eurydice_arr_f30 *t_as_ntt,
                                          Eurydice_arr_f30 *r_as_ntt,
                                          Eurydice_arr_f9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_f9 message_as_ring_element =
      deserialize_then_decompress_message_c5(message);
  Eurydice_arr_f9 v = compute_ring_element_v_e3(t_as_ntt, r_as_ntt, error_2,
                                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_4c(v, ciphertext);
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_unpacked_fa1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_56 ciphertext = {.data = {0U}};
  tuple_710 uu____0 =
      encrypt_c1_d51(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)640U, uint8_t *));
  Eurydice_arr_f30 r_as_ntt = uu____0.fst;
  Eurydice_arr_f9 error_2 = uu____0.snd;
  Eurydice_arr_f30 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_f30 *uu____2 = &r_as_ntt;
  Eurydice_arr_f9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_4c(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)768U, &ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
tuple_17 libcrux_ml_kem_ind_cca_unpacked_encapsulate_551(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_48(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_56 ciphertext = encrypt_unpacked_fa1(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static Eurydice_arr_f9 call_mut_35_4c(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE uint32x4_t decompress_uint32x4_t_ef(uint32x4_t v) {
  uint32x4_t coeff = _vdupq_n_u32(1U << (uint32_t)((int32_t)10 - (int32_t)1));
  uint32x4_t decompressed =
      _vmulq_n_u32(v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint32x4_t decompressed0 = _vaddq_u32(decompressed, coeff);
  return _vshrq_n_u32((int32_t)10, decompressed0, uint32x4_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_ef(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = decompress_uint32x4_t_ef(low00);
  uint32x4_t low1 = decompress_uint32x4_t_ef(low10);
  uint32x4_t high0 = decompress_uint32x4_t_ef(high00);
  uint32x4_t high1 = decompress_uint32x4_t_ef(high10);
  v.low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  v.high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_61 with const
generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_61_ef(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_ef(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_10_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_10_61(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_61_ef(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE uint32x4_t decompress_uint32x4_t_c4(uint32x4_t v) {
  uint32x4_t coeff = _vdupq_n_u32(1U << (uint32_t)((int32_t)11 - (int32_t)1));
  uint32x4_t decompressed =
      _vmulq_n_u32(v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint32x4_t decompressed0 = _vaddq_u32(decompressed, coeff);
  return _vshrq_n_u32((int32_t)11, decompressed0, uint32x4_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_c4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = decompress_uint32x4_t_c4(low00);
  uint32x4_t low1 = decompress_uint32x4_t_c4(low10);
  uint32x4_t high0 = decompress_uint32x4_t_c4(high00);
  uint32x4_t high1 = decompress_uint32x4_t_c4(high10);
  v.low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  v.high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_61 with const
generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_61_c4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_c4(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_11_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)22U,
                                 i0 * (size_t)22U + (size_t)22U, uint8_t *);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_11_61(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_61_c4(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_ring_element_u_0f(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_c5(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_0f(Eurydice_arr_f9 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_c5(&zeta_i, re);
  ntt_at_layer_2_c5(&zeta_i, re);
  ntt_at_layer_1_c5(&zeta_i, re);
  poly_barrett_reduce_d6_c5(re);
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
static KRML_MUSTINLINE Eurydice_arr_f30
deserialize_then_decompress_u_4c(Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_4c(&lvalue););
  Eurydice_arr_f30 u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_0f(u_bytes);
    ntt_vector_u_0f(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE uint32x4_t decompress_uint32x4_t_d1(uint32x4_t v) {
  uint32x4_t coeff = _vdupq_n_u32(1U << (uint32_t)((int32_t)4 - (int32_t)1));
  uint32x4_t decompressed =
      _vmulq_n_u32(v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint32x4_t decompressed0 = _vaddq_u32(decompressed, coeff);
  return _vshrq_n_u32((int32_t)4, decompressed0, uint32x4_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_d1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = decompress_uint32x4_t_d1(low00);
  uint32x4_t low1 = decompress_uint32x4_t_d1(low10);
  uint32x4_t high0 = decompress_uint32x4_t_d1(high00);
  uint32x4_t high1 = decompress_uint32x4_t_d1(high10);
  v.low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  v.high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_61 with const
generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_61_d1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_d1(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_4_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        libcrux_ml_kem_vector_neon_deserialize_4_61(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        decompress_ciphertext_coefficient_61_d1(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_uint32x4_t with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE uint32x4_t decompress_uint32x4_t_f4(uint32x4_t v) {
  uint32x4_t coeff = _vdupq_n_u32(1U << (uint32_t)((int32_t)5 - (int32_t)1));
  uint32x4_t decompressed =
      _vmulq_n_u32(v, (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  uint32x4_t decompressed0 = _vaddq_u32(decompressed, coeff);
  return _vshrq_n_u32((int32_t)5, decompressed0, uint32x4_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_f4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  uint32x4_t mask16 = _vdupq_n_u32(65535U);
  uint32x4_t low00 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
  uint32x4_t low10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.low), uint32x4_t);
  uint32x4_t high00 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
  uint32x4_t high10 =
      _vshrq_n_u32((int32_t)16, _vreinterpretq_u32_s16(v.high), uint32x4_t);
  uint32x4_t low0 = decompress_uint32x4_t_f4(low00);
  uint32x4_t low1 = decompress_uint32x4_t_f4(low10);
  uint32x4_t high0 = decompress_uint32x4_t_f4(high00);
  uint32x4_t high1 = decompress_uint32x4_t_f4(high10);
  v.low =
      _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
  v.high =
      _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
  return v;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.neon.decompress_ciphertext_coefficient_61 with const
generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
decompress_ciphertext_coefficient_61_f4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v) {
  return decompress_ciphertext_coefficient_f4(v);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_5_c5(Eurydice_slice serialized) {
  Eurydice_arr_f9 re = ZERO_d6_c5();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)10U,
                                 i0 * (size_t)10U + (size_t)10U, uint8_t *);
    re.data[i0] = libcrux_ml_kem_vector_neon_deserialize_5_61(bytes);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____1 =
        decompress_ciphertext_coefficient_61_f4(re.data[i0]);
    re.data[i0] = uu____1;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_ring_element_v_37(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_c5(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
subtract_reduce_c5(Eurydice_arr_f9 *myself, Eurydice_arr_f9 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
        coefficient_normal_form =
            libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
                b.data[i0], (int16_t)1441);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector diff =
        libcrux_ml_kem_vector_neon_sub_61(myself->data[i0],
                                          &coefficient_normal_form);
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector red =
        libcrux_ml_kem_vector_neon_barrett_reduce_61(diff);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_f9
subtract_reduce_d6_c5(Eurydice_arr_f9 *self, Eurydice_arr_f9 b) {
  return subtract_reduce_c5(self, b);
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
static KRML_MUSTINLINE Eurydice_arr_f9
compute_message_e3(Eurydice_arr_f9 *v, Eurydice_arr_f30 *secret_as_ntt,
                   Eurydice_arr_f30 *u_as_ntt) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_e3(&result, &product););
  invert_ntt_montgomery_e3(&result);
  return subtract_reduce_d6_c5(v, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_60
compress_then_serialize_message_c5(Eurydice_arr_f9 re) {
  Eurydice_arr_60 serialized = {.data = {0U}};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
          to_unsigned_field_modulus_c5(re.data[i0]);
      libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
          coefficient_compressed =
              libcrux_ml_kem_vector_neon_compress_1_61(coefficient);
      Eurydice_arr_8b bytes =
          libcrux_ml_kem_vector_neon_serialize_1_61(coefficient_compressed);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_c2(Eurydice_arr_f30 *secret_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_f30 u_as_ntt = deserialize_then_decompress_u_4c(ciphertext);
  Eurydice_arr_f9 v = deserialize_then_decompress_ring_element_v_37(
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_f9 message = compute_message_e3(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_c5(message);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_9e(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  Eurydice_arr_60 dummy = {.data = {0U}};
  libcrux_sha3_neon_x2_shake256(
      input, input, Eurydice_array_to_slice((size_t)32U, &digest, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &dummy, uint8_t));
  return digest;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 2
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_2d_49(Eurydice_slice input) {
  return PRF_9e(input);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa1(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_c2(
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
      G_2d_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
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
      PRF_2d_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext = encrypt_unpacked_fa1(
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
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
*/
static Eurydice_arr_f9 call_mut_0b_e3(void **_) { return ZERO_d6_c5(); }

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_f30
deserialize_ring_elements_reduced_out_e3(Eurydice_slice public_key) {
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_e3(&lvalue););
  Eurydice_arr_f30 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_e3(public_key, &deserialized_pk);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_37(
    Eurydice_arr_30 *public_key) {
  Eurydice_arr_f30 deserialized_pk =
      deserialize_ring_elements_reduced_out_e3(Eurydice_array_to_subslice_to(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_f30 *uu____0 = &deserialized_pk;
  Eurydice_arr_30 public_key_serialized = serialize_public_key_37(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_c1(
    Eurydice_arr_7f0 *private_key) {
  Eurydice_arr_60 t = H_2d_fd(Eurydice_array_to_subslice3(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_ac(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_c1(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair512
generate_keypair_cb1(Eurydice_slice key_generation_seed) {
  Eurydice_arr_f30 private_key = default_70_e3();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d public_key =
      default_8b_e3();
  generate_keypair_unpacked_c21(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_4c(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_c1(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, Eurydice_arr_7f0 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_7f0 *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_7f0 *uu____3 = serialized;
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
  Eurydice_arr_60 lvalue = H_2d_fd(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_7f0 *uu____7 = serialized;
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE Eurydice_arr_7f0 serialize_kem_secret_key_c1(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_7f0 out = {.data = {0U}};
  serialize_kem_secret_key_mut_c1(private_key, public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_ind_cca_generate_keypair_581(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_cb1(ind_cpa_keypair_randomness);
  Eurydice_arr_56 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_30 public_key = uu____0.snd;
  Eurydice_arr_7f0 secret_key_serialized = serialize_kem_secret_key_c1(
      Eurydice_array_to_slice((size_t)768U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_7f0 private_key =
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_48(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_4f1(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_e3(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_e21 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_cd1(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d
    build_unpacked_public_key_4f1(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d
      unpacked_public_key = default_8b_e3();
  build_unpacked_public_key_mut_4f1(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_fa1(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d
      unpacked_public_key = build_unpacked_public_key_4f1(public_key);
  return encrypt_unpacked_fa1(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_c1(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
tuple_17 libcrux_ml_kem_ind_cca_encapsulate_991(Eurydice_arr_30 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_48(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_2d_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_56 ciphertext =
      encrypt_fa1(Eurydice_array_to_slice(
                      (size_t)800U,
                      libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_56 uu____2 = libcrux_ml_kem_types_from_e0_d0(ciphertext);
  return (
      KRML_CLITERAL(tuple_17){.fst = uu____2, .snd = kdf_39_c1(shared_secret)});
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static Eurydice_arr_f9 call_mut_0b_c2(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_c2(Eurydice_slice secret_key,
                                                  Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_f30 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_c2(&lvalue););
  Eurydice_arr_f30 secret_key_unpacked = arr_struct;
  deserialize_vector_e3(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_c2(&secret_key_unpacked, ciphertext);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_761(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_c2(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
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
      PRF_2d_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext =
      encrypt_fa1(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_c1(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_c1(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, &expected_ciphertext, uint8_t),
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a5(
    Eurydice_slice public_key, Eurydice_arr_fe0 *deserialized_pk) {
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
    Eurydice_arr_f9 uu____0 =
        deserialize_to_reduced_ring_element_c5(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_e0(Eurydice_arr_84 *input) {
  Eurydice_arr_fe uu____0 = libcrux_sha3_neon_x2_incremental_init();
  Eurydice_arr_54 state = {
      .data = {uu____0, libcrux_sha3_neon_x2_incremental_init()}};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state.data, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      &state.data[1U],
      Eurydice_array_to_slice((size_t)34U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[2U], uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final_2d with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_2d_e0(Eurydice_arr_84 *input) {
  return shake128_init_absorb_final_e0(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_35
shake128_squeeze_first_three_blocks_e0(Eurydice_arr_54 *st) {
  Eurydice_arr_35 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  Eurydice_arr_b0 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->data, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      &st->data[1U], Eurydice_array_to_slice((size_t)504U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks_2d with
const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_35
shake128_squeeze_first_three_blocks_2d_e0(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_21(
    Eurydice_arr_35 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_d6
shake128_squeeze_next_block_e0(Eurydice_arr_54 *st) {
  Eurydice_arr_d6 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->data, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      &st->data[1U], Eurydice_array_to_slice((size_t)168U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block_2d with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_d6
shake128_squeeze_next_block_2d_e0(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_210(
    Eurydice_arr_d6 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static Eurydice_arr_f9 call_mut_e7_cd0(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_fe0
sample_from_xof_cd0(Eurydice_arr_84 *seeds) {
  Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_d4 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_54 xof_state = shake128_init_absorb_final_2d_e0(seeds);
  Eurydice_arr_35 randomness0 =
      shake128_squeeze_first_three_blocks_2d_e0(&xof_state);
  bool done = sample_from_uniform_distribution_next_21(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_d6 randomness =
          shake128_squeeze_next_block_2d_e0(&xof_state);
      done = sample_from_uniform_distribution_next_210(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_fe0 arr_mapped_str;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_cd0(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_cd0(Eurydice_arr_aa0 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_84 seeds; Eurydice_arr_480 repeat_expression[3U];
      KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)3U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_fe0 sampled = sample_from_xof_cd0(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)3U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_2d
with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_2d_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_H(input);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash,
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e0(
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a5(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_aa0 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_cd0(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_2d_e0(Eurydice_array_to_slice(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *
libcrux_ml_kem_ind_cca_unpacked_public_key_11_a5(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_91
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
clone_91_a5(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec *self) {
  Eurydice_arr_fe0 uu____0 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)3U, &self->t_as_ntt, Eurydice_arr_f9, Eurydice_arr_fe0);
  Eurydice_arr_60 uu____1 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->seed_for_A, uint8_t, Eurydice_arr_60);
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec){
          .t_as_ntt = uu____0,
          .seed_for_A = uu____1,
          .A = core_array__core__clone__Clone_for__Array_T__N___clone(
              (size_t)3U, &self->A, Eurydice_arr_fe0, Eurydice_arr_aa0)});
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_d7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
libcrux_ml_kem_ind_cca_unpacked_clone_d7_a5(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *self) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec uu____0 =
      clone_91_a5(&self->ind_cpa_public_key);
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec){
      .ind_cpa_public_key = uu____0,
      .public_key_hash = core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->public_key_hash, uint8_t, Eurydice_arr_60)});
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void serialize_vector_a5(Eurydice_arr_fe0 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, key, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_c5(&re);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_21(
    Eurydice_arr_fe0 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_74 *serialized) {
  serialize_vector_a5(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_21(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *self,
    Eurydice_arr_74 *serialized) {
  serialize_public_key_mut_21(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_21(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self,
    Eurydice_arr_74 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_21(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE Eurydice_arr_74
serialize_public_key_21(Eurydice_arr_fe0 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_74 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_21(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE Eurydice_arr_74 serialized_dd_21(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *self) {
  return libcrux_ml_kem_types_from_fd_d0(serialize_public_key_21(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_74 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_21(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self) {
  return serialized_dd_21(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair768
serialize_unpacked_secret_key_91(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_fe0 *private_key) {
  Eurydice_arr_74 public_key_serialized = serialize_public_key_21(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_600 secret_key_serialized = {.data = {0U}};
  serialize_vector_a5(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_b0(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self,
    Eurydice_arr_ea *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      serialize_unpacked_secret_key_91(&self->public_key.ind_cpa_public_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_ea libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_b0(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self) {
  Eurydice_arr_ea sk = libcrux_ml_kem_types_default_d3_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_b0(self, &sk);
  return sk;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_vector_a5(
    Eurydice_slice secret_key, Eurydice_arr_fe0 *secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          deserialize_to_uncompressed_ring_element_c5(Eurydice_slice_subslice3(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static Eurydice_arr_f9 call_mut_e7_560(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_fe0
sample_from_xof_560(Eurydice_arr_84 *seeds) {
  Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_d4 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_e4 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
          seeds);
  Eurydice_arr_35 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_21(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_d6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
              &xof_state);
      done = sample_from_uniform_distribution_next_210(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_fe0 arr_mapped_str;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_560(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_560(Eurydice_arr_aa0 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_84 seeds; Eurydice_arr_480 repeat_expression[3U];
      KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)3U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_fe0 sampled = sample_from_xof_560(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)3U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_440(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a5(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_aa0 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_560(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_36(
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_a5(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_440(ind_cpa_public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static Eurydice_arr_fe0 default_70_a5(void) {
  Eurydice_arr_fe0 lit;
  Eurydice_arr_f9 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_c5(););
  memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_f9));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec default_8b_a5(
    void) {
  Eurydice_arr_fe0 uu____0;
  Eurydice_arr_f9 repeat_expression0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_c5(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_f9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_fe0 repeat_expression1[3U];
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, Eurydice_arr_fe0 lit;
      Eurydice_arr_f9 repeat_expression[3U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_c5(););
      memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_f9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1,
         (size_t)3U * sizeof(Eurydice_arr_fe0));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
libcrux_ml_kem_ind_cca_unpacked_default_30_a5(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec){
          .ind_cpa_public_key = default_8b_a5(),
          .public_key_hash = {.data = {0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_a5(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ec uu____0 = {
      .ind_cpa_private_key = default_70_a5(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_a5()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_2d
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_2d_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_82(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  return G_2d_e0(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_41(Eurydice_arr_46 *input) {
  Eurydice_arr_db out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  Eurydice_arr_d1 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t));
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_2d
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_2d_41(Eurydice_arr_46 *input) {
  return PRFxN_41(input);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_1f0(
    Eurydice_arr_fe0 *re_as_ntt, Eurydice_arr_3e *prf_input,
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
  Eurydice_arr_db prf_outputs = PRFxN_2d_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_e3(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_c5(&re_as_ntt->data[i0]););
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_73_c20(void **_) { return ZERO_d6_c5(); }

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_a5(Eurydice_arr_f9 *myself,
                                                   Eurydice_arr_f9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_61(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_a5(Eurydice_arr_f9 *self,
                                                      Eurydice_arr_f9 *rhs) {
  add_to_ring_element_a5(self, rhs);
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
static KRML_MUSTINLINE void compute_As_plus_e_a5(
    Eurydice_arr_fe0 *t_as_ntt, Eurydice_arr_aa0 *matrix_A,
    Eurydice_arr_fe0 *s_as_ntt, Eurydice_arr_fe0 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, matrix_A, Eurydice_arr_fe0),
               Eurydice_arr_fe0);
       i++) {
    size_t i0 = i;
    Eurydice_arr_fe0 *row = &matrix_A->data[i0];
    Eurydice_arr_f9 uu____0 = ZERO_d6_c5();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_f9),
                  Eurydice_arr_f9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_f9 *matrix_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_a5(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_c5(&t_as_ntt->data[i0],
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_c20(
    Eurydice_slice key_generation_seed, Eurydice_arr_fe0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_82(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_aa0 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_cd0(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_1f0(private_key, &prf_input, 0U);
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_c20(&lvalue););
  Eurydice_arr_fe0 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_1f0(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_a5(&public_key->t_as_ntt, &public_key->A, private_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
*/
static Eurydice_arr_f9 call_mut_b4_a5(void **_) { return ZERO_d6_c5(); }

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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
*/
static Eurydice_arr_fe0 call_mut_7b_a5(void **_) {
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_a5(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static Eurydice_arr_aa0 transpose_a_a5(Eurydice_arr_aa0 ind_cpa_a) {
  Eurydice_arr_aa0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_a5(&lvalue););
  Eurydice_arr_aa0 A = arr_struct;
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          Eurydice_arr_f9 uu____0 = clone_c1_c5(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_580(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_c20(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_aa0 A = transpose_a_a5(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_74 pk_serialized = serialize_public_key_21(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_2d_e0(Eurydice_array_to_slice((size_t)1184U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_82(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_2d_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$3size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector

*/
typedef struct tuple_880_s {
  Eurydice_arr_fe0 fst;
  Eurydice_arr_f9 snd;
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_f1_d50(void **_) { return ZERO_d6_c5(); }

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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_dd_d50(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_1f0(
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_fe0 *error_1) {
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
  Eurydice_arr_db prf_outputs = PRFxN_2d_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          sample_from_binomial_distribution_e3(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_2d_410(Eurydice_slice input) {
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static Eurydice_arr_f9 call_mut_a8_a5(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_a5(Eurydice_arr_f9 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_c5(&zeta_i, re);
  invert_ntt_at_layer_2_c5(&zeta_i, re);
  invert_ntt_at_layer_3_c5(&zeta_i, re);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_c5(re);
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
static KRML_MUSTINLINE Eurydice_arr_fe0
compute_vector_u_a5(Eurydice_arr_aa0 *a_as_ntt, Eurydice_arr_fe0 *r_as_ntt,
                    Eurydice_arr_fe0 *error_1) {
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_a5(&lvalue););
  Eurydice_arr_fe0 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)3U, a_as_ntt, Eurydice_arr_fe0),
                Eurydice_arr_fe0);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_fe0 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_f9),
                 Eurydice_arr_f9);
         i++) {
      size_t j = i;
      Eurydice_arr_f9 *a_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_a5(&result.data[i1], &product);
    }
    invert_ntt_montgomery_a5(&result.data[i1]);
    add_error_reduce_d6_c5(&result.data[i1], &error_1->data[i1]);
  }
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
static KRML_MUSTINLINE void compress_then_serialize_u_b0(Eurydice_arr_fe0 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, &input, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_53(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_880 encrypt_c1_d50(Eurydice_slice randomness,
                                                Eurydice_arr_aa0 *matrix,
                                                Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_fe0 arr_struct0;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_d50(&lvalue););
  Eurydice_arr_fe0 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_1f0(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_d50(&lvalue););
  Eurydice_arr_fe0 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_1f0(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_2d_410(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_f9 error_2 = sample_from_binomial_distribution_e3(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_fe0 u = compute_vector_u_a5(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_b0(u, ciphertext);
  return (KRML_CLITERAL(tuple_880){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_f9 compute_ring_element_v_a5(
    Eurydice_arr_fe0 *t_as_ntt, Eurydice_arr_fe0 *r_as_ntt,
    Eurydice_arr_f9 *error_2, Eurydice_arr_f9 *message) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_a5(&result, &product););
  invert_ntt_montgomery_a5(&result);
  return add_message_error_reduce_d6_c5(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_91(
    Eurydice_arr_f9 re, Eurydice_slice out) {
  compress_then_serialize_4_c5(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_91(Eurydice_arr_fe0 *t_as_ntt,
                                          Eurydice_arr_fe0 *r_as_ntt,
                                          Eurydice_arr_f9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_f9 message_as_ring_element =
      deserialize_then_decompress_message_c5(message);
  Eurydice_arr_f9 v = compute_ring_element_v_a5(t_as_ntt, r_as_ntt, error_2,
                                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_91(v, ciphertext);
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_unpacked_fa0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_2c ciphertext = {.data = {0U}};
  tuple_880 uu____0 =
      encrypt_c1_d50(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)960U, uint8_t *));
  Eurydice_arr_fe0 r_as_ntt = uu____0.fst;
  Eurydice_arr_f9 error_2 = uu____0.snd;
  Eurydice_arr_fe0 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_fe0 *uu____2 = &r_as_ntt;
  Eurydice_arr_f9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_91(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1088U, &ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
tuple_56 libcrux_ml_kem_ind_cca_unpacked_encapsulate_550(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_82(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_2c ciphertext = encrypt_unpacked_fa0(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static Eurydice_arr_f9 call_mut_35_91(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE Eurydice_arr_fe0
deserialize_then_decompress_u_91(Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_91(&lvalue););
  Eurydice_arr_fe0 u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_0f(u_bytes);
    ntt_vector_u_0f(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_ring_element_v_21(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_c5(serialized);
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
static KRML_MUSTINLINE Eurydice_arr_f9
compute_message_a5(Eurydice_arr_f9 *v, Eurydice_arr_fe0 *secret_as_ntt,
                   Eurydice_arr_fe0 *u_as_ntt) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_a5(&result, &product););
  invert_ntt_montgomery_a5(&result);
  return subtract_reduce_d6_c5(v, result);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_36(Eurydice_arr_fe0 *secret_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_fe0 u_as_ntt = deserialize_then_decompress_u_91(ciphertext);
  Eurydice_arr_f9 v = deserialize_then_decompress_ring_element_v_21(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_f9 message = compute_message_a5(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_c5(message);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 3
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_2d_41(Eurydice_slice input) {
  return PRF_9e(input);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa0(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_36(
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
      G_2d_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_48 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_2d_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext = encrypt_unpacked_fa0(
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
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
*/
static Eurydice_arr_f9 call_mut_0b_a5(void **_) { return ZERO_d6_c5(); }

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_fe0
deserialize_ring_elements_reduced_out_a5(Eurydice_slice public_key) {
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_a5(&lvalue););
  Eurydice_arr_fe0 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_a5(public_key, &deserialized_pk);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_21(
    Eurydice_arr_74 *public_key) {
  Eurydice_arr_fe0 deserialized_pk =
      deserialize_ring_elements_reduced_out_a5(Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_fe0 *uu____0 = &deserialized_pk;
  Eurydice_arr_74 public_key_serialized = serialize_public_key_21(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_20(
    Eurydice_arr_ea *private_key) {
  Eurydice_arr_60 t = H_2d_e0(Eurydice_array_to_subslice3(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_a5(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_20(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair768
generate_keypair_cb0(Eurydice_slice key_generation_seed) {
  Eurydice_arr_fe0 private_key = default_70_a5();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec public_key =
      default_8b_a5();
  generate_keypair_unpacked_c20(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_91(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_20(
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
  Eurydice_arr_60 lvalue = H_2d_e0(public_key);
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE Eurydice_arr_ea serialize_kem_secret_key_20(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_ea out = {.data = {0U}};
  serialize_kem_secret_key_mut_20(private_key, public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_580(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_cb0(ind_cpa_keypair_randomness);
  Eurydice_arr_600 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_74 public_key = uu____0.snd;
  Eurydice_arr_ea secret_key_serialized = serialize_kem_secret_key_20(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_82(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_4f0(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a5(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_aa0 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_cd0(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
    build_unpacked_public_key_4f0(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
      unpacked_public_key = default_8b_a5();
  build_unpacked_public_key_mut_4f0(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_fa0(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec
      unpacked_public_key = build_unpacked_public_key_4f0(public_key);
  return encrypt_unpacked_fa0(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_20(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
tuple_56 libcrux_ml_kem_ind_cca_encapsulate_990(Eurydice_arr_74 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_82(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_2d_e0(Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_2c ciphertext =
      encrypt_fa0(Eurydice_array_to_slice(
                      (size_t)1184U,
                      libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_2c uu____2 = libcrux_ml_kem_types_from_e0_80(ciphertext);
  return (
      KRML_CLITERAL(tuple_56){.fst = uu____2, .snd = kdf_39_20(shared_secret)});
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static Eurydice_arr_f9 call_mut_0b_36(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_36(Eurydice_slice secret_key,
                                                  Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_fe0 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_36(&lvalue););
  Eurydice_arr_fe0 secret_key_unpacked = arr_struct;
  deserialize_vector_a5(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_36(&secret_key_unpacked, ciphertext);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_760(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_36(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_48 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_2d_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext =
      encrypt_fa0(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_20(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_20(shared_secret0);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_40(
    Eurydice_slice public_key, Eurydice_arr_7f *deserialized_pk) {
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
    Eurydice_arr_f9 uu____0 =
        deserialize_to_reduced_ring_element_c5(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_ac(Eurydice_arr_78 *input) {
  Eurydice_arr_fe uu____0 = libcrux_sha3_neon_x2_incremental_init();
  Eurydice_arr_54 state = {
      .data = {uu____0, libcrux_sha3_neon_x2_incremental_init()}};
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      state.data, Eurydice_array_to_slice((size_t)34U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[1U], uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
      &state.data[1U],
      Eurydice_array_to_slice((size_t)34U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)34U, &input->data[3U], uint8_t));
  return state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_init_absorb_final_2d with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_54
shake128_init_absorb_final_2d_ac(Eurydice_arr_78 *input) {
  return shake128_init_absorb_final_ac(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_ec
shake128_squeeze_first_three_blocks_ac(Eurydice_arr_54 *st) {
  Eurydice_arr_ec out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_b0 out0 = {.data = {0U}};
  Eurydice_arr_b0 out1 = {.data = {0U}};
  Eurydice_arr_b0 out2 = {.data = {0U}};
  Eurydice_arr_b0 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      st->data, Eurydice_array_to_slice((size_t)504U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out1, uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
      &st->data[1U], Eurydice_array_to_slice((size_t)504U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  out.data[3U] = out3;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_first_three_blocks_2d with
const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_ec
shake128_squeeze_first_three_blocks_2d_ac(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_a1(
    Eurydice_arr_ec *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_a6
shake128_squeeze_next_block_ac(Eurydice_arr_54 *st) {
  Eurydice_arr_a6 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_27 out0 = {.data = {0U}};
  Eurydice_arr_27 out1 = {.data = {0U}};
  Eurydice_arr_27 out2 = {.data = {0U}};
  Eurydice_arr_27 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      st->data, Eurydice_array_to_slice((size_t)168U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out1, uint8_t));
  libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
      &st->data[1U], Eurydice_array_to_slice((size_t)168U, &out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, &out3, uint8_t));
  out.data[0U] = out0;
  out.data[1U] = out1;
  out.data[2U] = out2;
  out.data[3U] = out3;
  return out;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.neon.shake128_squeeze_next_block_2d with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_a6
shake128_squeeze_next_block_2d_ac(Eurydice_arr_54 *self) {
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_a10(
    Eurydice_arr_a6 *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_neon_rej_sample_61(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static Eurydice_arr_f9 call_mut_e7_cd(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_7f
sample_from_xof_cd(Eurydice_arr_78 *seeds) {
  Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8a out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_54 xof_state = shake128_init_absorb_final_2d_ac(seeds);
  Eurydice_arr_ec randomness0 =
      shake128_squeeze_first_three_blocks_2d_ac(&xof_state);
  bool done = sample_from_uniform_distribution_next_a1(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a6 randomness =
          shake128_squeeze_next_block_2d_ac(&xof_state);
      done = sample_from_uniform_distribution_next_a10(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_7f arr_mapped_str;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_cd(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_cd(Eurydice_arr_95 *A_transpose,
                                               Eurydice_arr_480 *seed,
                                               bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_78 seeds; Eurydice_arr_480 repeat_expression[4U];
      KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)4U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_7f sampled = sample_from_xof_cd(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)4U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.H_2d
with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_60 H_2d_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_H(input);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash,
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1568U, public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_40(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_95 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_cd(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_2d_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void serialize_vector_40(Eurydice_arr_7f *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, key, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_c5(&re);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_a1(
    Eurydice_arr_7f *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_00 *serialized) {
  serialize_vector_40(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_a1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *self,
    Eurydice_arr_00 *serialized) {
  serialize_public_key_mut_a1(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_a1(
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_a1(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE Eurydice_arr_00
serialize_public_key_a1(Eurydice_arr_7f *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_00 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_a1(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE Eurydice_arr_00 serialized_dd_a1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *self) {
  return libcrux_ml_kem_types_from_fd_af(serialize_public_key_a1(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_00 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_a1(
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self) {
  return serialized_dd_a1(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair1024
serialize_unpacked_secret_key_4d(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 *public_key,
    Eurydice_arr_7f *private_key) {
  Eurydice_arr_00 public_key_serialized = serialize_public_key_a1(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_38 secret_key_serialized = {.data = {0U}};
  serialize_vector_40(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_fd(
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self,
    Eurydice_arr_17 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      serialize_unpacked_secret_key_4d(&self->public_key.ind_cpa_public_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_17 libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_fd(
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self) {
  Eurydice_arr_17 sk = libcrux_ml_kem_types_default_d3_39();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_fd(self, &sk);
  return sk;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_vector_40(
    Eurydice_slice secret_key, Eurydice_arr_7f *secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          deserialize_to_uncompressed_ring_element_c5(Eurydice_slice_subslice3(
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static Eurydice_arr_f9 call_mut_e7_56(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_c5(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_7f
sample_from_xof_56(Eurydice_arr_78 *seeds) {
  Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8a out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_180 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
          seeds);
  Eurydice_arr_ec randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_a1(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
              &xof_state);
      done = sample_from_uniform_distribution_next_a10(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_7f arr_mapped_str;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_56(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_56(Eurydice_arr_95 *A_transpose,
                                               Eurydice_arr_480 *seed,
                                               bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_78 seeds; Eurydice_arr_480 repeat_expression[4U];
      KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)4U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_7f sampled = sample_from_xof_56(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)4U, &sampled,
                                                          Eurydice_arr_f9),
                                  Eurydice_arr_f9);
           i++) {
        size_t j = i;
        Eurydice_arr_f9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
        }
      });
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_44(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_40(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_95 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_56(uu____1, &lvalue, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_21(
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_40(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_44(ind_cpa_public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static Eurydice_arr_7f default_70_40(void) {
  Eurydice_arr_7f lit;
  Eurydice_arr_f9 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_c5(););
  memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_f9));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 default_8b_40(
    void) {
  Eurydice_arr_7f uu____0;
  Eurydice_arr_f9 repeat_expression0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_c5(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_f9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_7f repeat_expression1[4U];
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, Eurydice_arr_7f lit;
      Eurydice_arr_f9 repeat_expression[4U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_c5(););
      memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_f9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1, (size_t)4U * sizeof(Eurydice_arr_7f));
  return lit0;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56
libcrux_ml_kem_ind_cca_unpacked_default_30_40(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56){
          .ind_cpa_public_key = default_8b_40(),
          .public_key_hash = {.data = {0U}}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_40(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_56 uu____0 = {
      .ind_cpa_private_key = default_70_40(),
      .implicit_rejection_value = {.data = {0U}}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_40()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.G_2d
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_2d_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_neon_G(input);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_49(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  return G_2d_ac(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_44(Eurydice_arr_65 *input) {
  Eurydice_arr_cc0 out = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_d1 out0 = {.data = {0U}};
  Eurydice_arr_d1 out1 = {.data = {0U}};
  Eurydice_arr_d1 out2 = {.data = {0U}};
  Eurydice_arr_d1 out3 = {.data = {0U}};
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, input->data, uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[1U], uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out0, uint8_t),
      Eurydice_array_to_slice((size_t)128U, &out1, uint8_t));
  libcrux_sha3_neon_x2_shake256(
      Eurydice_array_to_slice((size_t)33U, &input->data[2U], uint8_t),
      Eurydice_array_to_slice((size_t)33U, &input->data[3U], uint8_t),
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
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRFxN_2d
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_2d_44(Eurydice_arr_65 *input) {
  return PRFxN_44(input);
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
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_1f(
    Eurydice_arr_7f *re_as_ntt, Eurydice_arr_3e *prf_input,
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
  Eurydice_arr_cc0 prf_outputs = PRFxN_2d_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_e3(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_c5(&re_as_ntt->data[i0]););
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_73_c2(void **_) { return ZERO_d6_c5(); }

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_40(Eurydice_arr_f9 *myself,
                                                   Eurydice_arr_f9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself,
                   libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector),
               libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector uu____0 =
        libcrux_ml_kem_vector_neon_add_61(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_40(Eurydice_arr_f9 *self,
                                                      Eurydice_arr_f9 *rhs) {
  add_to_ring_element_40(self, rhs);
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
static KRML_MUSTINLINE void compute_As_plus_e_40(
    Eurydice_arr_7f *t_as_ntt, Eurydice_arr_95 *matrix_A,
    Eurydice_arr_7f *s_as_ntt, Eurydice_arr_7f *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, matrix_A, Eurydice_arr_7f),
               Eurydice_arr_7f);
       i++) {
    size_t i0 = i;
    Eurydice_arr_7f *row = &matrix_A->data[i0];
    Eurydice_arr_f9 uu____0 = ZERO_d6_c5();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_f9),
                  Eurydice_arr_f9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_f9 *matrix_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_40(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_c5(&t_as_ntt->data[i0],
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_c2(
    Eurydice_slice key_generation_seed, Eurydice_arr_7f *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_49(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_95 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_cd(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_1f(private_key, &prf_input, 0U);
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_c2(&lvalue););
  Eurydice_arr_7f error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_1f(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_40(&public_key->t_as_ntt, &public_key->A, private_key,
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
*/
static Eurydice_arr_f9 call_mut_b4_40(void **_) { return ZERO_d6_c5(); }

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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
*/
static Eurydice_arr_7f call_mut_7b_40(void **_) {
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_40(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static Eurydice_arr_95 transpose_a_40(Eurydice_arr_95 ind_cpa_a) {
  Eurydice_arr_95 arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_40(&lvalue););
  Eurydice_arr_95 A = arr_struct;
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          Eurydice_arr_f9 uu____0 = clone_c1_c5(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_58(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_c2(ind_cpa_keypair_randomness,
                               &out->private_key.ind_cpa_private_key,
                               &out->public_key.ind_cpa_public_key);
  Eurydice_arr_95 A = transpose_a_40(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_00 pk_serialized = serialize_public_key_a1(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_2d_ac(Eurydice_array_to_slice((size_t)1568U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_49(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_2d_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$4size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector

*/
typedef struct tuple_0c_s {
  Eurydice_arr_7f fst;
  Eurydice_arr_f9 snd;
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_f1_d5(void **_) { return ZERO_d6_c5(); }

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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static Eurydice_arr_f9 call_mut_dd_d5(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE uint8_t
sample_ring_element_cbd_1f(Eurydice_arr_3e *prf_input, uint8_t domain_separator,
                           Eurydice_arr_7f *error_1) {
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
  Eurydice_arr_cc0 prf_outputs = PRFxN_2d_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_f9 uu____0 =
          sample_from_binomial_distribution_e3(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_2d_440(Eurydice_slice input) {
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static Eurydice_arr_f9 call_mut_a8_40(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_40(Eurydice_arr_f9 *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_c5(&zeta_i, re);
  invert_ntt_at_layer_2_c5(&zeta_i, re);
  invert_ntt_at_layer_3_c5(&zeta_i, re);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_c5(re);
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
static KRML_MUSTINLINE Eurydice_arr_7f
compute_vector_u_40(Eurydice_arr_95 *a_as_ntt, Eurydice_arr_7f *r_as_ntt,
                    Eurydice_arr_7f *error_1) {
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_40(&lvalue););
  Eurydice_arr_7f result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)4U, a_as_ntt, Eurydice_arr_7f),
                Eurydice_arr_7f);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_7f *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_f9),
                 Eurydice_arr_f9);
         i++) {
      size_t j = i;
      Eurydice_arr_f9 *a_element = &row->data[j];
      Eurydice_arr_f9 product =
          ntt_multiply_d6_c5(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_40(&result.data[i1], &product);
    }
    invert_ntt_montgomery_40(&result.data[i1]);
    add_error_reduce_d6_c5(&result.data[i1], &error_1->data[i1]);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_11_88(Eurydice_arr_f9 *re) {
  Eurydice_arr_79 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficient =
        compress_61_c4(libcrux_ml_kem_vector_neon_to_unsigned_representative_61(
            re->data[i0]));
    Eurydice_arr_f3 bytes =
        libcrux_ml_kem_vector_neon_serialize_11_61(coefficient);
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_ring_element_u_f3(Eurydice_arr_f9 *re) {
  return compress_then_serialize_11_88(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_fd(Eurydice_arr_7f input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, &input, Eurydice_arr_f9),
               Eurydice_arr_f9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_f9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_79 lvalue = compress_then_serialize_ring_element_u_f3(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)352U, &lvalue, uint8_t),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_0c encrypt_c1_d5(Eurydice_slice randomness,
                                              Eurydice_arr_95 *matrix,
                                              Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_7f arr_struct0;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_d5(&lvalue););
  Eurydice_arr_7f r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_1f(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_d5(&lvalue););
  Eurydice_arr_7f error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_1f(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_2d_440(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_f9 error_2 = sample_from_binomial_distribution_e3(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_7f u = compute_vector_u_40(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_fd(u, ciphertext);
  return (KRML_CLITERAL(tuple_0c){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_f9
compute_ring_element_v_40(Eurydice_arr_7f *t_as_ntt, Eurydice_arr_7f *r_as_ntt,
                          Eurydice_arr_f9 *error_2, Eurydice_arr_f9 *message) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_40(&result, &product););
  invert_ntt_montgomery_40(&result);
  return add_message_error_reduce_d6_c5(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_4d(
    Eurydice_arr_f9 re, Eurydice_slice out) {
  compress_then_serialize_5_c5(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_4d(Eurydice_arr_7f *t_as_ntt,
                                          Eurydice_arr_7f *r_as_ntt,
                                          Eurydice_arr_f9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_f9 message_as_ring_element =
      deserialize_then_decompress_message_c5(message);
  Eurydice_arr_f9 v = compute_ring_element_v_40(t_as_ntt, r_as_ntt, error_2,
                                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_4d(v, ciphertext);
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_unpacked_fa(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_00 ciphertext = {.data = {0U}};
  tuple_0c uu____0 =
      encrypt_c1_d5(randomness, &public_key->A,
                    Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                (size_t)1408U, uint8_t *));
  Eurydice_arr_7f r_as_ntt = uu____0.fst;
  Eurydice_arr_f9 error_2 = uu____0.snd;
  Eurydice_arr_7f *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_7f *uu____2 = &r_as_ntt;
  Eurydice_arr_f9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_4d(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1568U, &ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
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
tuple_2b libcrux_ml_kem_ind_cca_unpacked_encapsulate_55(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_49(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_00 ciphertext = encrypt_unpacked_fa(
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
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static Eurydice_arr_f9 call_mut_35_4d(void **_) { return ZERO_d6_c5(); }

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_ring_element_u_34(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_c5(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_34(Eurydice_arr_f9 *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_c5(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_c5(&zeta_i, re);
  ntt_at_layer_2_c5(&zeta_i, re);
  ntt_at_layer_1_c5(&zeta_i, re);
  poly_barrett_reduce_d6_c5(re);
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
static KRML_MUSTINLINE Eurydice_arr_7f
deserialize_then_decompress_u_4d(Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_4d(&lvalue););
  Eurydice_arr_7f u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_34(u_bytes);
    ntt_vector_u_34(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE Eurydice_arr_f9
deserialize_then_decompress_ring_element_v_a1(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_c5(serialized);
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
static KRML_MUSTINLINE Eurydice_arr_f9
compute_message_40(Eurydice_arr_f9 *v, Eurydice_arr_7f *secret_as_ntt,
                   Eurydice_arr_7f *u_as_ntt) {
  Eurydice_arr_f9 result = ZERO_d6_c5();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_f9 product = ntt_multiply_d6_c5(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_40(&result, &product););
  invert_ntt_montgomery_40(&result);
  return subtract_reduce_d6_c5(v, result);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_21(Eurydice_arr_7f *secret_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_7f u_as_ntt = deserialize_then_decompress_u_4d(ciphertext);
  Eurydice_arr_f9 v = deserialize_then_decompress_ring_element_v_a1(
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_f9 message = compute_message_40(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_c5(message);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::neon::Simd128Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.neon.PRF_2d
with const generics
- K= 4
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_2d_44(Eurydice_slice input) {
  return PRF_9e(input);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa(
    libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_21(
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
      G_2d_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
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
      PRF_2d_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext = encrypt_unpacked_fa(
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
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
*/
static Eurydice_arr_f9 call_mut_0b_40(void **_) { return ZERO_d6_c5(); }

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_7f
deserialize_ring_elements_reduced_out_40(Eurydice_slice public_key) {
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_40(&lvalue););
  Eurydice_arr_7f deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_40(public_key, &deserialized_pk);
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_a1(
    Eurydice_arr_00 *public_key) {
  Eurydice_arr_7f deserialized_pk =
      deserialize_ring_elements_reduced_out_40(Eurydice_array_to_subslice_to(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_7f *uu____0 = &deserialized_pk;
  Eurydice_arr_00 public_key_serialized = serialize_public_key_a1(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_1f(
    Eurydice_arr_17 *private_key) {
  Eurydice_arr_60 t = H_2d_ac(Eurydice_array_to_subslice3(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_ba(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_1f(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair1024
generate_keypair_cb(Eurydice_slice key_generation_seed) {
  Eurydice_arr_7f private_key = default_70_40();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 public_key =
      default_8b_40();
  generate_keypair_unpacked_c2(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_4d(&public_key, &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_1f(
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
  Eurydice_arr_60 lvalue = H_2d_ac(public_key);
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE Eurydice_arr_17 serialize_kem_secret_key_1f(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_17 out = {.data = {0U}};
  serialize_kem_secret_key_mut_1f(private_key, public_key,
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_58(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_cb(ind_cpa_keypair_randomness);
  Eurydice_arr_38 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_00 public_key = uu____0.snd;
  Eurydice_arr_17 secret_key_serialized = serialize_kem_secret_key_1f(
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
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_49(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_4f(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_40(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_95 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_cd(uu____1, &lvalue, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56
    build_unpacked_public_key_4f(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56
      unpacked_public_key = default_8b_40();
  build_unpacked_public_key_mut_4f(public_key, &unpacked_public_key);
  return unpacked_public_key;
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_fa(Eurydice_slice public_key,
                                                  Eurydice_arr_60 *message,
                                                  Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56
      unpacked_public_key = build_unpacked_public_key_4f(public_key);
  return encrypt_unpacked_fa(&unpacked_public_key, message, randomness);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_1f(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
tuple_2b libcrux_ml_kem_ind_cca_encapsulate_99(Eurydice_arr_00 *public_key,
                                               Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_49(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_2d_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_00 ciphertext =
      encrypt_fa(Eurydice_array_to_slice(
                     (size_t)1568U,
                     libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t),
                 &randomness0, pseudorandomness);
  Eurydice_arr_00 uu____2 = libcrux_ml_kem_types_from_e0_af(ciphertext);
  return (
      KRML_CLITERAL(tuple_2b){.fst = uu____2, .snd = kdf_39_1f(shared_secret)});
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
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static Eurydice_arr_f9 call_mut_0b_21(void **_) { return ZERO_d6_c5(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_21(Eurydice_slice secret_key,
                                                  Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_7f arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_21(&lvalue););
  Eurydice_arr_7f secret_key_unpacked = arr_struct;
  deserialize_vector_40(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_21(&secret_key_unpacked, ciphertext);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_76(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_21(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_2d_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
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
      PRF_2d_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext =
      encrypt_fa(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_1f(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_1f(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
}
