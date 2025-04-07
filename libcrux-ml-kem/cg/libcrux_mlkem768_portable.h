/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 763350c6948d5594d3017ecb93273bc41c1a4e1d
 * Eurydice: 36a5ed7dd6b61b5cd3d69a010859005912d21537
 * Karamel: bf9b89d76dd24e2ceaaca32de3535353e7b6bc01
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: f3f15359a852405a81628f982f2debc4d50fff30
 */

#ifndef __libcrux_mlkem768_portable_H
#define __libcrux_mlkem768_portable_H

#include "eurydice_glue.h"
#include "libcrux_ct_ops.h"
#include "libcrux_mlkem_core.h"
#include "libcrux_sha3_portable.h"

static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_G(
    Eurydice_slice input, uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_H(
    Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

static const int16_t libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[128U] =
    {(int16_t)-1044, (int16_t)-758,  (int16_t)-359,  (int16_t)-1517,
     (int16_t)1493,  (int16_t)1422,  (int16_t)287,   (int16_t)202,
     (int16_t)-171,  (int16_t)622,   (int16_t)1577,  (int16_t)182,
     (int16_t)962,   (int16_t)-1202, (int16_t)-1474, (int16_t)1468,
     (int16_t)573,   (int16_t)-1325, (int16_t)264,   (int16_t)383,
     (int16_t)-829,  (int16_t)1458,  (int16_t)-1602, (int16_t)-130,
     (int16_t)-681,  (int16_t)1017,  (int16_t)732,   (int16_t)608,
     (int16_t)-1542, (int16_t)411,   (int16_t)-205,  (int16_t)-1571,
     (int16_t)1223,  (int16_t)652,   (int16_t)-552,  (int16_t)1015,
     (int16_t)-1293, (int16_t)1491,  (int16_t)-282,  (int16_t)-1544,
     (int16_t)516,   (int16_t)-8,    (int16_t)-320,  (int16_t)-666,
     (int16_t)-1618, (int16_t)-1162, (int16_t)126,   (int16_t)1469,
     (int16_t)-853,  (int16_t)-90,   (int16_t)-271,  (int16_t)830,
     (int16_t)107,   (int16_t)-1421, (int16_t)-247,  (int16_t)-951,
     (int16_t)-398,  (int16_t)961,   (int16_t)-1508, (int16_t)-725,
     (int16_t)448,   (int16_t)-1065, (int16_t)677,   (int16_t)-1275,
     (int16_t)-1103, (int16_t)430,   (int16_t)555,   (int16_t)843,
     (int16_t)-1251, (int16_t)871,   (int16_t)1550,  (int16_t)105,
     (int16_t)422,   (int16_t)587,   (int16_t)177,   (int16_t)-235,
     (int16_t)-291,  (int16_t)-460,  (int16_t)1574,  (int16_t)1653,
     (int16_t)-246,  (int16_t)778,   (int16_t)1159,  (int16_t)-147,
     (int16_t)-777,  (int16_t)1483,  (int16_t)-602,  (int16_t)1119,
     (int16_t)-1590, (int16_t)644,   (int16_t)-872,  (int16_t)349,
     (int16_t)418,   (int16_t)329,   (int16_t)-156,  (int16_t)-75,
     (int16_t)817,   (int16_t)1097,  (int16_t)603,   (int16_t)610,
     (int16_t)1322,  (int16_t)-1285, (int16_t)-1465, (int16_t)384,
     (int16_t)-1215, (int16_t)-136,  (int16_t)1218,  (int16_t)-1335,
     (int16_t)-874,  (int16_t)220,   (int16_t)-1187, (int16_t)-1659,
     (int16_t)-1185, (int16_t)-1530, (int16_t)-1278, (int16_t)794,
     (int16_t)-1510, (int16_t)-854,  (int16_t)-870,  (int16_t)478,
     (int16_t)-108,  (int16_t)-308,  (int16_t)996,   (int16_t)991,
     (int16_t)958,   (int16_t)-1460, (int16_t)1522,  (int16_t)1628};

static KRML_MUSTINLINE int16_t libcrux_ml_kem_polynomial_zeta(size_t i) {
  return libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[i];
}

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT  \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / \
   LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS ((int16_t)3329)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS \
  ((int16_t)1353)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (62209U)

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_s {
  int16_t elements[16U];
} libcrux_ml_kem_vector_portable_vector_type_PortableVector;

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  int16_t ret[16U];
  Result_0a dst;
  Eurydice_slice_to_array2(
      &dst, Eurydice_slice_subslice2(array, (size_t)0U, (size_t)16U, int16_t),
      Eurydice_slice, int16_t[16U], TryFromSliceError);
  unwrap_26_00(dst, ret);
  memcpy(lit.elements, ret, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_from_i16_array_2c(Eurydice_slice array) {
  return libcrux_ml_kem_vector_portable_vector_type_from_i16_array(array);
}

typedef struct int16_t_x8_s {
  int16_t fst;
  int16_t snd;
  int16_t thd;
  int16_t f3;
  int16_t f4;
  int16_t f5;
  int16_t f6;
  int16_t f7;
} int16_t_x8;

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_zero(void) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  int16_t repeat_expression[16U] = {0U};
  memcpy(lit.elements, repeat_expression, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ZERO_2c(void) {
  return libcrux_ml_kem_vector_portable_vector_type_zero();
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_add(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.elements[uu____0] = lhs.elements[uu____0] + rhs->elements[i0];
  }
  return lhs;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_add_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_sub(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.elements[uu____0] = lhs.elements[uu____0] - rhs->elements[i0];
  }
  return lhs;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_sub_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.elements[uu____0] = vec.elements[uu____0] * c;
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_multiply_by_constant_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  return libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.elements[uu____0] = vec.elements[uu____0] & c;
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_bitwise_and_with_constant_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c) {
  return libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(v,
                                                                             c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (vec.elements[i0] >= (int16_t)3329) {
      size_t uu____0 = i0;
      vec.elements[uu____0] = vec.elements[uu____0] - (int16_t)3329;
    }
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_cond_subtract_3329_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v) {
  return libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(v);
}

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int32_t)20159)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT ((int32_t)26)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_R \
  ((int32_t)1 << (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT)

/**
 Signed Barrett Reduction

 Given an input `value`, `barrett_reduce` outputs a representative `result`
 such that:

 - result ≡ value (mod FIELD_MODULUS)
 - the absolute value of `result` is bound as follows:

 `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)

 Note: The input bound is 28296 to prevent overflow in the multiplication of
 quotient by FIELD_MODULUS

*/
static inline int16_t
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value) {
  int32_t t = (int32_t)value *
                  LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER +
              (LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient =
      (int16_t)(t >> (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  return value - quotient * LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec.elements[i0]);
    vec.elements[i0] = vi;
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_barrett_reduce_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v) {
  return libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(v);
}

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (16U)

/**
 Signed Montgomery Reduction

 Given an input `value`, `montgomery_reduce` outputs a representative `o`
 such that:

 - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
 - the absolute value of `o` is bound as follows:

 `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665

 In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS-1`. And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS + 1664

*/
static inline int16_t
libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
    int32_t value) {
  int32_t k =
      (int32_t)(int16_t)value *
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
  int32_t k_times_modulus =
      (int32_t)(int16_t)k * (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
  int16_t c =
      (int16_t)(k_times_modulus >>
                (uint32_t)
                    LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high =
      (int16_t)(value >>
                (uint32_t)
                    LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
static KRML_MUSTINLINE int16_t
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer) {
  int32_t product = (int32_t)fe * (int32_t)fer;
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.elements[i0] =
        libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec.elements[i0], c);
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t r) {
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      v, r);
}

/**
 The `compress_*` functions implement the `Compress` function specified in the
 NIST FIPS 203 standard (Page 18, Expression 4.5), which is defined as:

 ```plaintext
 Compress_d: ℤq -> ℤ_{2ᵈ}
 Compress_d(x) = ⌈(2ᵈ/q)·x⌋
 ```

 Since `⌈x⌋ = ⌊x + 1/2⌋` we have:

 ```plaintext
 Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
               = ⌊(2^{d+1}·x + q) / 2q⌋
 ```

 For further information about the function implementations, consult the
 `implementation_notes.pdf` document in this directory.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
static inline uint8_t
libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe) {
  int16_t shifted = (int16_t)1664 - (int16_t)fe;
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range = shifted_to_positive - (int16_t)832;
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & (int16_t)1;
  return (uint8_t)r1;
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_compress_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    a.elements[i0] = (int16_t)
        libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
            (uint16_t)a.elements[i0]);
  }
  return a;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_1_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_compress_1(a);
}

static KRML_MUSTINLINE uint32_t
libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  return value & ((1U << (uint32_t)n) - 1U);
}

static inline int16_t
libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = (uint64_t)fe << (uint32_t)coefficient_bits;
  compressed = compressed + 1664ULL;
  compressed = compressed * 10321340ULL;
  compressed = compressed >> 35U;
  return (int16_t)
      libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, (uint32_t)compressed);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->elements[j], zeta);
  int16_t a_minus_t = vec->elements[i] - t;
  int16_t a_plus_t = vec->elements[i] + t;
  vec->elements[j] = a_minus_t;
  vec->elements[i] = a_plus_t;
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)0U,
                                              (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)1U,
                                              (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)4U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)5U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta2, (size_t)8U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta2, (size_t)9U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta3, (size_t)12U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta3, (size_t)13U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_1_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                             zeta2, zeta3);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)0U,
                                              (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)1U,
                                              (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)2U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)3U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)8U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)9U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)10U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)11U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_2_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)0U,
                                              (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)1U,
                                              (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)2U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)3U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)4U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)5U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)6U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)7U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_3_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = vec->elements[j] - vec->elements[i];
  int16_t a_plus_b = vec->elements[j] + vec->elements[i];
  int16_t o0 = libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
      a_plus_b);
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta);
  vec->elements[i] = o0;
  vec->elements[j] = o1;
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)0U,
                                                  (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)1U,
                                                  (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)4U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)5U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta2, (size_t)8U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta2, (size_t)9U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta3, (size_t)12U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta3, (size_t)13U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
      a, zeta0, zeta1, zeta2, zeta3);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)0U,
                                                  (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)1U,
                                                  (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)2U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)3U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)8U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)9U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)10U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)11U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0,
                                                                 zeta1);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)0U,
                                                  (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)1U,
                                                  (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)2U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)3U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)4U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)5U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)6U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)7U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
}

/**
 Compute the product of two Kyber binomials with respect to the
 modulus `X² - zeta`.

 This function almost implements <strong>Algorithm 11</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
 Input: γ ∈ ℤq.
 Output: c₀, c₁ ∈ ℤq.

 c₀ ← a₀·b₀ + a₁·b₁·γ
 c₁ ← a₀·b₁ + a₁·b₀
 return c₀, c₁
 ```
 We say "almost" because the coefficients output by this function are in
 the Montgomery domain (unlike in the specification).

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *b, int16_t zeta,
    size_t i, libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t ai = a->elements[(size_t)2U * i];
  int16_t bi = b->elements[(size_t)2U * i];
  int16_t aj = a->elements[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->elements[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = (int32_t)ai * (int32_t)bi;
  int32_t aj_bj_ = (int32_t)aj * (int32_t)bj;
  int16_t aj_bj =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          aj_bj_);
  int32_t aj_bj_zeta = (int32_t)aj_bj * (int32_t)zeta;
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int16_t o0 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bi_aj_bj);
  int32_t ai_bj = (int32_t)ai * (int32_t)bj;
  int32_t aj_bi = (int32_t)aj * (int32_t)bi;
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bj_aj_bi);
  int16_t _out0[16U];
  memcpy(_out0, out->elements, (size_t)16U * sizeof(int16_t));
  out->elements[(size_t)2U * i] = o0;
  out->elements[(size_t)2U * i + (size_t)1U] = o1;
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector out =
      libcrux_ml_kem_vector_portable_vector_type_zero();
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, zeta0,
                                                            (size_t)0U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, nzeta0,
                                                            (size_t)1U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, zeta1,
                                                            (size_t)2U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, nzeta1,
                                                            (size_t)3U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, zeta2,
                                                            (size_t)4U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, nzeta2,
                                                            (size_t)5U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, zeta3,
                                                            (size_t)6U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(lhs, rhs, nzeta3,
                                                            (size_t)7U, &out);
  return out;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_multiply_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_multiply(lhs, rhs, zeta0, zeta1,
                                                         zeta2, zeta3);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[2U]) {
  uint8_t result0 = (((((((uint32_t)(uint8_t)v.elements[0U] |
                          (uint32_t)(uint8_t)v.elements[1U] << 1U) |
                         (uint32_t)(uint8_t)v.elements[2U] << 2U) |
                        (uint32_t)(uint8_t)v.elements[3U] << 3U) |
                       (uint32_t)(uint8_t)v.elements[4U] << 4U) |
                      (uint32_t)(uint8_t)v.elements[5U] << 5U) |
                     (uint32_t)(uint8_t)v.elements[6U] << 6U) |
                    (uint32_t)(uint8_t)v.elements[7U] << 7U;
  uint8_t result1 = (((((((uint32_t)(uint8_t)v.elements[8U] |
                          (uint32_t)(uint8_t)v.elements[9U] << 1U) |
                         (uint32_t)(uint8_t)v.elements[10U] << 2U) |
                        (uint32_t)(uint8_t)v.elements[11U] << 3U) |
                       (uint32_t)(uint8_t)v.elements[12U] << 4U) |
                      (uint32_t)(uint8_t)v.elements[13U] << 5U) |
                     (uint32_t)(uint8_t)v.elements[14U] << 6U) |
                    (uint32_t)(uint8_t)v.elements[15U] << 7U;
  ret[0U] = result0;
  ret[1U] = result1;
}

static inline void libcrux_ml_kem_vector_portable_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[2U]) {
  libcrux_ml_kem_vector_portable_serialize_serialize_1(a, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_1_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[2U]) {
  libcrux_ml_kem_vector_portable_serialize_1(a, ret);
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_1(Eurydice_slice v) {
  int16_t result0 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) &
                              1U);
  int16_t result1 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  1U &
                              1U);
  int16_t result2 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  2U &
                              1U);
  int16_t result3 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  3U &
                              1U);
  int16_t result4 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  4U &
                              1U);
  int16_t result5 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  5U &
                              1U);
  int16_t result6 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  6U &
                              1U);
  int16_t result7 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)0U, uint8_t, uint8_t *) >>
                                  7U &
                              1U);
  int16_t result8 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)1U, uint8_t, uint8_t *) &
                              1U);
  int16_t result9 = (int16_t)((uint32_t)Eurydice_slice_index(
                                  v, (size_t)1U, uint8_t, uint8_t *) >>
                                  1U &
                              1U);
  int16_t result10 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   2U &
                               1U);
  int16_t result11 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   3U &
                               1U);
  int16_t result12 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   4U &
                               1U);
  int16_t result13 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   5U &
                               1U);
  int16_t result14 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   6U &
                               1U);
  int16_t result15 = (int16_t)((uint32_t)Eurydice_slice_index(
                                   v, (size_t)1U, uint8_t, uint8_t *) >>
                                   7U &
                               1U);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  lit.elements[0U] = result0;
  lit.elements[1U] = result1;
  lit.elements[2U] = result2;
  lit.elements[3U] = result3;
  lit.elements[4U] = result4;
  lit.elements[5U] = result5;
  lit.elements[6U] = result6;
  lit.elements[7U] = result7;
  lit.elements[8U] = result8;
  lit.elements[9U] = result9;
  lit.elements[10U] = result10;
  lit.elements[11U] = result11;
  lit.elements[12U] = result12;
  lit.elements[13U] = result13;
  lit.elements[14U] = result14;
  lit.elements[15U] = result15;
  return lit;
}

static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_1(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_1(a);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_1_2c(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_1(a);
}

typedef struct uint8_t_x4_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
} uint8_t_x4;

static KRML_MUSTINLINE uint8_t_x4
libcrux_ml_kem_vector_portable_serialize_serialize_4_int(Eurydice_slice v) {
  uint8_t result0 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)0U, int16_t,
                                              int16_t *);
  uint8_t result1 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)2U, int16_t,
                                              int16_t *);
  uint8_t result2 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)4U, int16_t,
                                              int16_t *);
  uint8_t result3 =
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *)
          << 4U |
      (uint32_t)(uint8_t)Eurydice_slice_index(v, (size_t)6U, int16_t,
                                              int16_t *);
  return (uint8_t_x4{result0, result1, result2, result3});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[8U]) {
  uint8_t_x4 result0_3 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice2(v.elements, (size_t)0U, (size_t)8U,
                                      int16_t));
  uint8_t_x4 result4_7 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice2(v.elements, (size_t)8U, (size_t)16U,
                                      int16_t));
  ret[0U] = result0_3.fst;
  ret[1U] = result0_3.snd;
  ret[2U] = result0_3.thd;
  ret[3U] = result0_3.f3;
  ret[4U] = result4_7.fst;
  ret[5U] = result4_7.snd;
  ret[6U] = result4_7.thd;
  ret[7U] = result4_7.f3;
}

static inline void libcrux_ml_kem_vector_portable_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[8U]) {
  libcrux_ml_kem_vector_portable_serialize_serialize_4(a, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_4_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[8U]) {
  libcrux_ml_kem_vector_portable_serialize_4(a, ret);
}

static KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes) {
  int16_t v0 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v1 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)0U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v2 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v3 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)1U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v4 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v5 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)2U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  int16_t v6 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) &
                         15U);
  int16_t v7 = (int16_t)((uint32_t)Eurydice_slice_index(bytes, (size_t)3U,
                                                        uint8_t, uint8_t *) >>
                             4U &
                         15U);
  return (int16_t_x8{v0, v1, v2, v3, v4, v5, v6, v7});
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_4(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)4U, uint8_t));
  int16_t_x8 v8_15 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice2(bytes, (size_t)4U, (size_t)8U, uint8_t));
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  lit.elements[0U] = v0_7.fst;
  lit.elements[1U] = v0_7.snd;
  lit.elements[2U] = v0_7.thd;
  lit.elements[3U] = v0_7.f3;
  lit.elements[4U] = v0_7.f4;
  lit.elements[5U] = v0_7.f5;
  lit.elements[6U] = v0_7.f6;
  lit.elements[7U] = v0_7.f7;
  lit.elements[8U] = v8_15.fst;
  lit.elements[9U] = v8_15.snd;
  lit.elements[10U] = v8_15.thd;
  lit.elements[11U] = v8_15.f3;
  lit.elements[12U] = v8_15.f4;
  lit.elements[13U] = v8_15.f5;
  lit.elements[14U] = v8_15.f6;
  lit.elements[15U] = v8_15.f7;
  return lit;
}

static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_4(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_4(a);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_4_2c(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_4(a);
}

typedef struct uint8_t_x5_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
} uint8_t_x5;

static KRML_MUSTINLINE uint8_t_x5
libcrux_ml_kem_vector_portable_serialize_serialize_10_int(Eurydice_slice v) {
  uint8_t r0 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) &
                (int16_t)255);
  uint8_t r1 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) &
                                   (int16_t)63)
                   << 2U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t,
                                                        int16_t *) >>
                                       8U &
                                   (int16_t)3);
  uint8_t r2 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) &
                                   (int16_t)15)
                   << 4U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t,
                                                        int16_t *) >>
                                       6U &
                                   (int16_t)15);
  uint8_t r3 = (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t,
                                                        int16_t *) &
                                   (int16_t)3)
                   << 6U |
               (uint32_t)(uint8_t)(Eurydice_slice_index(v, (size_t)2U, int16_t,
                                                        int16_t *) >>
                                       4U &
                                   (int16_t)63);
  uint8_t r4 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 2U &
                (int16_t)255);
  return (uint8_t_x5{r0, r1, r2, r3, r4});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[20U]) {
  uint8_t_x5 r0_4 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)0U, (size_t)4U, int16_t));
  uint8_t_x5 r5_9 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)4U, (size_t)8U, int16_t));
  uint8_t_x5 r10_14 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)8U, (size_t)12U,
                                  int16_t));
  uint8_t_x5 r15_19 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)12U, (size_t)16U,
                                  int16_t));
  ret[0U] = r0_4.fst;
  ret[1U] = r0_4.snd;
  ret[2U] = r0_4.thd;
  ret[3U] = r0_4.f3;
  ret[4U] = r0_4.f4;
  ret[5U] = r5_9.fst;
  ret[6U] = r5_9.snd;
  ret[7U] = r5_9.thd;
  ret[8U] = r5_9.f3;
  ret[9U] = r5_9.f4;
  ret[10U] = r10_14.fst;
  ret[11U] = r10_14.snd;
  ret[12U] = r10_14.thd;
  ret[13U] = r10_14.f3;
  ret[14U] = r10_14.f4;
  ret[15U] = r15_19.fst;
  ret[16U] = r15_19.snd;
  ret[17U] = r15_19.thd;
  ret[18U] = r15_19.f3;
  ret[19U] = r15_19.f4;
}

static inline void libcrux_ml_kem_vector_portable_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[20U]) {
  libcrux_ml_kem_vector_portable_serialize_serialize_10(a, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_10_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[20U]) {
  libcrux_ml_kem_vector_portable_serialize_10(a, ret);
}

static KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes) {
  int16_t r0 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
       (int16_t)3)
          << 8U |
      ((int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) &
       (int16_t)255);
  int16_t r1 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
       (int16_t)15)
          << 6U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          2U;
  int16_t r2 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) &
       (int16_t)63)
          << 4U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          4U;
  int16_t r3 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *)
          << 2U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          6U;
  int16_t r4 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) &
       (int16_t)3)
          << 8U |
      ((int16_t)Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *) &
       (int16_t)255);
  int16_t r5 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *) &
       (int16_t)15)
          << 6U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *) >>
          2U;
  int16_t r6 =
      ((int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) &
       (int16_t)63)
          << 4U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *) >>
          4U;
  int16_t r7 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *)
          << 2U |
      (int16_t)Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *) >>
          6U;
  return (int16_t_x8{r0, r1, r2, r3, r4, r5, r6, r7});
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_10(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)10U, uint8_t));
  int16_t_x8 v8_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice2(bytes, (size_t)10U, (size_t)20U, uint8_t));
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  lit.elements[0U] = v0_7.fst;
  lit.elements[1U] = v0_7.snd;
  lit.elements[2U] = v0_7.thd;
  lit.elements[3U] = v0_7.f3;
  lit.elements[4U] = v0_7.f4;
  lit.elements[5U] = v0_7.f5;
  lit.elements[6U] = v0_7.f6;
  lit.elements[7U] = v0_7.f7;
  lit.elements[8U] = v8_15.fst;
  lit.elements[9U] = v8_15.snd;
  lit.elements[10U] = v8_15.thd;
  lit.elements[11U] = v8_15.f3;
  lit.elements[12U] = v8_15.f4;
  lit.elements[13U] = v8_15.f5;
  lit.elements[14U] = v8_15.f6;
  lit.elements[15U] = v8_15.f7;
  return lit;
}

static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_10(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_10(a);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_10_2c(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_10(a);
}

typedef struct uint8_t_x3_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
} uint8_t_x3;

static KRML_MUSTINLINE uint8_t_x3
libcrux_ml_kem_vector_portable_serialize_serialize_12_int(Eurydice_slice v) {
  uint8_t r0 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) &
                (int16_t)255);
  uint8_t r1 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U |
                (Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) &
                 (int16_t)15)
                    << 4U);
  uint8_t r2 =
      (uint8_t)(Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 4U &
                (int16_t)255);
  return (uint8_t_x3{r0, r1, r2});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[24U]) {
  uint8_t_x3 r0_2 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)0U, (size_t)2U, int16_t));
  uint8_t_x3 r3_5 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)2U, (size_t)4U, int16_t));
  uint8_t_x3 r6_8 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)4U, (size_t)6U, int16_t));
  uint8_t_x3 r9_11 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)6U, (size_t)8U, int16_t));
  uint8_t_x3 r12_14 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)8U, (size_t)10U,
                                  int16_t));
  uint8_t_x3 r15_17 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)10U, (size_t)12U,
                                  int16_t));
  uint8_t_x3 r18_20 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)12U, (size_t)14U,
                                  int16_t));
  uint8_t_x3 r21_23 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice2(v.elements, (size_t)14U, (size_t)16U,
                                  int16_t));
  ret[0U] = r0_2.fst;
  ret[1U] = r0_2.snd;
  ret[2U] = r0_2.thd;
  ret[3U] = r3_5.fst;
  ret[4U] = r3_5.snd;
  ret[5U] = r3_5.thd;
  ret[6U] = r6_8.fst;
  ret[7U] = r6_8.snd;
  ret[8U] = r6_8.thd;
  ret[9U] = r9_11.fst;
  ret[10U] = r9_11.snd;
  ret[11U] = r9_11.thd;
  ret[12U] = r12_14.fst;
  ret[13U] = r12_14.snd;
  ret[14U] = r12_14.thd;
  ret[15U] = r15_17.fst;
  ret[16U] = r15_17.snd;
  ret[17U] = r15_17.thd;
  ret[18U] = r18_20.fst;
  ret[19U] = r18_20.snd;
  ret[20U] = r18_20.thd;
  ret[21U] = r21_23.fst;
  ret[22U] = r21_23.snd;
  ret[23U] = r21_23.thd;
}

static inline void libcrux_ml_kem_vector_portable_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[24U]) {
  libcrux_ml_kem_vector_portable_serialize_serialize_12(a, ret);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_12_2c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[24U]) {
  libcrux_ml_kem_vector_portable_serialize_12(a, ret);
}

typedef struct int16_t_x2_s {
  int16_t fst;
  int16_t snd;
} int16_t_x2;

static KRML_MUSTINLINE int16_t_x2
libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes) {
  int16_t byte0 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
  int16_t byte1 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
  int16_t byte2 =
      (int16_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
  int16_t r0 = (byte1 & (int16_t)15) << 8U | (byte0 & (int16_t)255);
  int16_t r1 = byte2 << 4U | (byte1 >> 4U & (int16_t)15);
  return (int16_t_x2{r0, r1});
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_12(Eurydice_slice bytes) {
  int16_t_x2 v0_1 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice2(bytes, (size_t)0U, (size_t)3U, uint8_t));
  int16_t_x2 v2_3 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice2(bytes, (size_t)3U, (size_t)6U, uint8_t));
  int16_t_x2 v4_5 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice2(bytes, (size_t)6U, (size_t)9U, uint8_t));
  int16_t_x2 v6_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice2(bytes, (size_t)9U, (size_t)12U, uint8_t));
  int16_t_x2 v8_9 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice2(bytes, (size_t)12U, (size_t)15U, uint8_t));
  int16_t_x2 v10_11 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice2(bytes, (size_t)15U, (size_t)18U, uint8_t));
  int16_t_x2 v12_13 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice2(bytes, (size_t)18U, (size_t)21U, uint8_t));
  int16_t_x2 v14_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice2(bytes, (size_t)21U, (size_t)24U, uint8_t));
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  lit.elements[0U] = v0_1.fst;
  lit.elements[1U] = v0_1.snd;
  lit.elements[2U] = v2_3.fst;
  lit.elements[3U] = v2_3.snd;
  lit.elements[4U] = v4_5.fst;
  lit.elements[5U] = v4_5.snd;
  lit.elements[6U] = v6_7.fst;
  lit.elements[7U] = v6_7.snd;
  lit.elements[8U] = v8_9.fst;
  lit.elements[9U] = v8_9.snd;
  lit.elements[10U] = v10_11.fst;
  lit.elements[11U] = v10_11.snd;
  lit.elements[12U] = v12_13.fst;
  lit.elements[13U] = v12_13.snd;
  lit.elements[14U] = v14_15.fst;
  lit.elements[15U] = v14_15.snd;
  return lit;
}

static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_12(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_12(a);
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_12_2c(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_12(a);
}

static KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_portable_sampling_rej_sample(Eurydice_slice a,
                                                   Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(a, uint8_t) / (size_t)3U;
       i++) {
    size_t i0 = i;
    int16_t b1 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)0U,
                                               uint8_t, uint8_t *);
    int16_t b2 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)1U,
                                               uint8_t, uint8_t *);
    int16_t b3 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)2U,
                                               uint8_t, uint8_t *);
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
  return sampled;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
static inline size_t libcrux_ml_kem_vector_portable_rej_sample_2c(
    Eurydice_slice a, Eurydice_slice out) {
  return libcrux_ml_kem_vector_portable_sampling_rej_sample(a, out);
}

#define LIBCRUX_ML_KEM_MLKEM768_VECTOR_U_COMPRESSION_FACTOR ((size_t)10U)

#define LIBCRUX_ML_KEM_MLKEM768_C1_BLOCK_SIZE              \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * \
   LIBCRUX_ML_KEM_MLKEM768_VECTOR_U_COMPRESSION_FACTOR / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_RANK ((size_t)3U)

#define LIBCRUX_ML_KEM_MLKEM768_C1_SIZE \
  (LIBCRUX_ML_KEM_MLKEM768_C1_BLOCK_SIZE * LIBCRUX_ML_KEM_MLKEM768_RANK)

#define LIBCRUX_ML_KEM_MLKEM768_VECTOR_V_COMPRESSION_FACTOR ((size_t)4U)

#define LIBCRUX_ML_KEM_MLKEM768_C2_SIZE                    \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * \
   LIBCRUX_ML_KEM_MLKEM768_VECTOR_V_COMPRESSION_FACTOR / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE \
  (LIBCRUX_ML_KEM_MLKEM768_C1_SIZE + LIBCRUX_ML_KEM_MLKEM768_C2_SIZE)

#define LIBCRUX_ML_KEM_MLKEM768_T_AS_NTT_ENCODED_SIZE      \
  (LIBCRUX_ML_KEM_MLKEM768_RANK *                          \
   LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * \
   LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_PUBLIC_KEY_SIZE \
  (LIBCRUX_ML_KEM_MLKEM768_T_AS_NTT_ENCODED_SIZE + (size_t)32U)

#define LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_SECRET_KEY_SIZE    \
  (LIBCRUX_ML_KEM_MLKEM768_RANK *                          \
   LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * \
   LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_ETA1 ((size_t)2U)

#define LIBCRUX_ML_KEM_MLKEM768_ETA1_RANDOMNESS_SIZE \
  (LIBCRUX_ML_KEM_MLKEM768_ETA1 * (size_t)64U)

#define LIBCRUX_ML_KEM_MLKEM768_ETA2 ((size_t)2U)

#define LIBCRUX_ML_KEM_MLKEM768_ETA2_RANDOMNESS_SIZE \
  (LIBCRUX_ML_KEM_MLKEM768_ETA2 * (size_t)64U)

#define LIBCRUX_ML_KEM_MLKEM768_IMPLICIT_REJECTION_HASH_INPUT_SIZE \
  (LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE +                   \
   LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_CIPHERTEXT_SIZE)

typedef libcrux_ml_kem_types_MlKemPrivateKey_d9
    libcrux_ml_kem_mlkem768_MlKem768PrivateKey;

typedef libcrux_ml_kem_types_MlKemPublicKey_30
    libcrux_ml_kem_mlkem768_MlKem768PublicKey;

#define LIBCRUX_ML_KEM_MLKEM768_RANKED_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_MLKEM768_RANK *                             \
   LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_SECRET_KEY_SIZE      \
  (LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_SECRET_KEY_SIZE + \
   LIBCRUX_ML_KEM_MLKEM768_CPA_PKE_PUBLIC_KEY_SIZE + \
   LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE +          \
   LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE)

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_1d_s {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_1d;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0;

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_ZERO_ef_96(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector
      repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_2c();
  }
  memcpy(lit.coefficients, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_96(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_deserialize_12_2c(bytes);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_deserialize_vector_1b(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_96(
            Eurydice_slice_subslice2(
                secret_key,
                i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                (i0 + (size_t)1U) *
                    LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                uint8_t));
    secret_as_ntt[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = (int32_t)a.elements[i0] *
                           (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a.elements[i0] = (int16_t)decompressed;
  }
  return a;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_2c with const
generics
- COEFFICIENT_BITS= 10
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_2c_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_ef(
      a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_then_decompress_10_96(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)20U, i0 * (size_t)20U + (size_t)20U, uint8_t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_10_2c(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_2c_ef(
            coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_0a(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_10_96(serialized);
}

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2_s {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector fst;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector snd;
} libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2;

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_traits_montgomery_multiply_fe_96(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t fer) {
  return libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(v,
                                                                           fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    libcrux_ml_kem_ntt_ntt_layer_int_vec_step_96(
        libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
        libcrux_ml_kem_vector_portable_vector_type_PortableVector b,
        int16_t zeta_r) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
      libcrux_ml_kem_vector_traits_montgomery_multiply_fe_96(b, zeta_r);
  b = libcrux_ml_kem_vector_portable_sub_2c(a, &t);
  a = libcrux_ml_kem_vector_portable_add_2c(a, &t);
  return (libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2{a, b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
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
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2 uu____0 =
          libcrux_ml_kem_ntt_ntt_layer_int_vec_step_96(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_portable_vector_type_PortableVector x = uu____0.fst;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_3_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_ntt_layer_3_step_2c(
            re->coefficients[round],
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
    re->coefficients[round] = uu____0;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_2_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_portable_ntt_layer_2_step_2c(
            re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_1_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_portable_ntt_layer_1_step_2c(
            re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)2U),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)3U));
    zeta_i[0U] = zeta_i[0U] + (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_2c(
            myself->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  libcrux_ml_kem_polynomial_poly_barrett_reduce_96(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_vector_u_0a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i = (size_t)0U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)7U,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)6U,
                                            (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)5U,
                                            (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)4U,
                                            (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_96(&zeta_i, re, (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_96(&zeta_i, re, (size_t)6U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_96(&zeta_i, re, (size_t)7U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_ef_96(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_6c(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    u_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
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
        libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_0a(
            u_bytes);
    libcrux_ml_kem_ntt_ntt_vector_u_0a(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = (int32_t)a.elements[i0] *
                           (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a.elements[i0] = (int16_t)decompressed;
  }
  return a;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_2c with const
generics
- COEFFICIENT_BITS= 4
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_2c_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_d1(
      a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_then_decompress_4_96(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_4_2c(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_2c_d1(
            coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_89(
    Eurydice_slice serialized) {
  return libcrux_ml_kem_serialize_deserialize_then_decompress_4_96(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_ZERO_96(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector
      repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_2c();
  }
  memcpy(lit.coefficients, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
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
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_ntt_multiply_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d out =
      libcrux_ml_kem_polynomial_ZERO_96();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_ntt_multiply_2c(
            &myself->coefficients[i0], &rhs->coefficients[i0],
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)1U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)2U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)3U));
    out.coefficients[i0] = uu____0;
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_ntt_multiply_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  return libcrux_ml_kem_polynomial_ntt_multiply_96(self, rhs);
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself->coefficients,
                   libcrux_ml_kem_vector_portable_vector_type_PortableVector),
               libcrux_ml_kem_vector_portable_vector_type_PortableVector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_add_2c(myself->coefficients[i0],
                                              &rhs->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_ef_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  libcrux_ml_kem_polynomial_add_to_ring_element_1b(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_2c(
            re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)2U),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)3U));
    zeta_i[0U] = zeta_i[0U] - (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    re->coefficients[round] =
        libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_2c(
            re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_2c(
            re->coefficients[round],
            libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
    re->coefficients[round] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_96(
        libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
        libcrux_ml_kem_vector_portable_vector_type_PortableVector b,
        int16_t zeta_r) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector a_minus_b =
      libcrux_ml_kem_vector_portable_sub_2c(b, &a);
  a = libcrux_ml_kem_vector_portable_barrett_reduce_2c(
      libcrux_ml_kem_vector_portable_add_2c(a, &b));
  b = libcrux_ml_kem_vector_traits_montgomery_multiply_fe_96(a_minus_b, zeta_r);
  return (libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2{a, b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_96(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
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
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2 uu____0 =
          libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_96(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_portable_vector_type_PortableVector x = uu____0.fst;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_96(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_96(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_96(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_96(&zeta_i, re,
                                                          (size_t)4U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_96(&zeta_i, re,
                                                          (size_t)5U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_96(&zeta_i, re,
                                                          (size_t)6U);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_96(&zeta_i, re,
                                                          (size_t)7U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_ef_96(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_subtract_reduce_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(
                b.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_2c(
            libcrux_ml_kem_vector_portable_sub_2c(myself->coefficients[i0],
                                                  &coefficient_normal_form));
    b.coefficients[i0] = uu____0;
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_subtract_reduce_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d b) {
  return libcrux_ml_kem_polynomial_subtract_reduce_96(self, b);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_matrix_compute_message_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
        libcrux_ml_kem_polynomial_ntt_multiply_ef_96(&secret_as_ntt[i0],
                                                     &u_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_ef_1b(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(&result);
  return libcrux_ml_kem_polynomial_subtract_reduce_ef_96(v, result);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_shift_right_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.elements[i0] = vec.elements[i0] >> (uint32_t)(int32_t)15;
  }
  return vec;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.shift_right_2c
with const generics
- SHIFT_BY= 15
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_shift_right_2c_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v) {
  return libcrux_ml_kem_vector_portable_arithmetic_shift_right_ef(v);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_traits_to_unsigned_representative_96(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
      libcrux_ml_kem_vector_portable_shift_right_2c_ef(a);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector fm =
      libcrux_ml_kem_vector_portable_bitwise_and_with_constant_2c(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_portable_add_2c(a, &fm);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_serialize_to_unsigned_field_modulus_96(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_traits_to_unsigned_representative_96(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_message_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_serialize_to_unsigned_field_modulus_96(
            re.coefficients[i0]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_compressed =
            libcrux_ml_kem_vector_portable_compress_1_2c(coefficient);
    uint8_t bytes[2U];
    libcrux_ml_kem_vector_portable_serialize_1_2c(coefficient_compressed,
                                                  bytes);
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_decrypt_unpacked_42(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[3U];
  libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_6c(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_89(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t,
                                          __builtin_slice_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message =
      libcrux_ml_kem_matrix_compute_message_1b(&v, secret_key->secret_as_ntt,
                                               u_as_ntt);
  uint8_t ret0[32U];
  libcrux_ml_kem_serialize_compress_then_serialize_message_96(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_decrypt_42(
    Eurydice_slice secret_key, uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret0[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_deserialize_vector_1b(
      secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_42(&secret_key_unpacked, ciphertext,
                                             ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.G_f1
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_G_f1_e0(
    Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_portable_G(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRF_9e(
    Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_f1
with const generics
- K= 3
- LEN= 32
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRF_f1_41(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_portable_PRF_9e(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8d
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_default_8d_1b(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    uu____0[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression0[3U][3U];
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[3U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      repeat_expression[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
    }
    memcpy(repeat_expression0[i0], repeat_expression,
           (size_t)3U *
               sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  }
  memcpy(lit.A, repeat_expression0,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
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
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_96(
    Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice2(
        serialized, i0 * (size_t)24U, i0 * (size_t)24U + (size_t)24U, uint8_t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_12_2c(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_cond_subtract_3329_2c(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *deserialized_pk) {
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_96(
            ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PortableHash
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_hash_functions_portable_PortableHash_88_s {
  libcrux_sha3_generic_keccak_KeccakState_17 shake128_state[3U];
} libcrux_ml_kem_hash_functions_portable_PortableHash_88;

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash_88
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_e0(
    uint8_t (*input)[34U]) {
  libcrux_ml_kem_hash_functions_portable_PortableHash_88 shake128_state;
  libcrux_sha3_generic_keccak_KeccakState_17 repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = libcrux_sha3_portable_incremental_shake128_init();
  }
  memcpy(shake128_state.shake128_state, repeat_expression,
         (size_t)3U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_absorb_final(
        &shake128_state.shake128_state[i0],
        Eurydice_array_to_slice((size_t)34U, input[i0], uint8_t));
  }
  return shake128_state;
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final_f1 with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash_88
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_f1_e0(
    uint8_t (*input)[34U]) {
  return libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_e0(
      input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *st,
    uint8_t ret[3U][504U]) {
  uint8_t out[3U][504U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
        &st->shake128_state[i0],
        Eurydice_array_to_slice((size_t)504U, out[i0], uint8_t));
  }
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks_f1
with const generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_f1_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *self,
    uint8_t ret[3U][504U]) {
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_e0(
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
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_89(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
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
        size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_2c(
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
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block with const
generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *st,
    uint8_t ret[3U][168U]) {
  uint8_t out[3U][168U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
        &st->shake128_state[i0],
        Eurydice_array_to_slice((size_t)168U, out[i0], uint8_t));
  }
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block_f1 with const
generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_f1_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *self,
    uint8_t ret[3U][168U]) {
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_e0(self,
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
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_890(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
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
        size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_2c(
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
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_from_i16_array_96(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result =
      libcrux_ml_kem_polynomial_ZERO_96();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_from_i16_array_2c(
            Eurydice_slice_subslice2(a, i0 * (size_t)16U,
                                     (i0 + (size_t)1U) * (size_t)16U, int16_t));
    result.coefficients[i0] = uu____0;
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_from_i16_array_ef_96(Eurydice_slice a) {
  return libcrux_ml_kem_polynomial_from_i16_array_96(a);
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.closure
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_sampling_sample_from_xof_closure_2b(int16_t s[272U]) {
  return libcrux_ml_kem_polynomial_from_i16_array_ef_96(
      Eurydice_array_to_subslice2(s, (size_t)0U, (size_t)256U, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_2b(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_PortableHash_88 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_f1_e0(
          seeds);
  uint8_t randomness0[3U][504U];
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_f1_e0(
      &xof_state, randomness0);
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_89(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_f1_e0(
          &xof_state, randomness);
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_890(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret0[i] =
        libcrux_ml_kem_sampling_sample_from_xof_closure_2b(copy_of_out[i]);
  }
  memcpy(
      ret, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_2b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*A_transpose)[3U],
    uint8_t *seed, bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    uint8_t seeds[3U][34U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      core_array___core__clone__Clone_for__Array_T__N___20__clone(
          (size_t)34U, seed, seeds[i], uint8_t, void *);
    }
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds[j][32U] = (uint8_t)i1;
      seeds[j][33U] = (uint8_t)j;
    }
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d sampled[3U];
    libcrux_ml_kem_sampling_sample_from_xof_2b(seeds, sampled);
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, sampled,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d sample = sampled[j];
      if (transpose) {
        A_transpose[j][i1] = sample;
      } else {
        A_transpose[i1][j] = sample;
      }
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_3f(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, __builtin_slice_t);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, __builtin_slice_t);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[3U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_2b(uu____1, ret, false);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
    libcrux_ml_kem_ind_cpa_build_unpacked_public_key_3f(
        Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_8d_1b();
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_3f(public_key,
                                                          &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[3size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_ed_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d fst[3U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d snd;
} tuple_ed;

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRFxN_41(
    uint8_t (*input)[33U], uint8_t ret[3U][128U]) {
  uint8_t out[3U][128U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_sha3_portable_shake256(
        Eurydice_array_to_slice((size_t)128U, out[i0], uint8_t),
        Eurydice_array_to_slice((size_t)33U, input[i0], uint8_t));
  }
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN_f1
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRFxN_f1_41(
    uint8_t (*input)[33U], uint8_t ret[3U][128U]) {
  libcrux_ml_kem_hash_functions_portable_PRFxN_41(input, ret);
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
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_96(
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
  return libcrux_ml_kem_polynomial_from_i16_array_ef_96(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
    Eurydice_slice randomness) {
  return libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_96(
      randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_7_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
        libcrux_ml_kem_vector_portable_multiply_by_constant_2c(
            re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_portable_sub_2c(re->coefficients[j], &t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____1 =
        libcrux_ml_kem_vector_portable_add_2c(re->coefficients[j], &t);
    re->coefficients[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  libcrux_ml_kem_ntt_ntt_at_layer_7_96(re);
  size_t zeta_i = (size_t)1U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)6U,
                                            (size_t)11207U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(&zeta_i, re, (size_t)5U,
                                            (size_t)11207U + (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_96(
      &zeta_i, re, (size_t)4U, (size_t)11207U + (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_96(
      &zeta_i, re, (size_t)11207U + (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_96(
      &zeta_i, re, (size_t)11207U + (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_96(
      &zeta_i, re, (size_t)11207U + (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_ef_96(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_3b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    core_array___core__clone__Clone_for__Array_T__N___20__clone(
        (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *);
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  libcrux_ml_kem_hash_functions_portable_PRFxN_f1_41(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    re_as_ntt[i0] =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_96(&re_as_ntt[i0]);
  }
  return domain_separator;
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_3b(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1) {
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    core_array___core__clone__Clone_for__Array_T__N___20__clone(
        (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *);
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  libcrux_ml_kem_hash_functions_portable_PRFxN_f1_41(prf_inputs, prf_outputs);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
            Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
    error_1[i0] = uu____0;
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRF_a6(
    Eurydice_slice input, uint8_t ret[128U]) {
  uint8_t digest[128U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)128U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_f1
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_PRF_f1_410(
    Eurydice_slice input, uint8_t ret[128U]) {
  libcrux_ml_kem_hash_functions_portable_PRF_a6(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(
                myself->coefficients[j], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_2c(
            libcrux_ml_kem_vector_portable_add_2c(coefficient_normal_form,
                                                  &error->coefficients[j]));
    myself->coefficients[j] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  libcrux_ml_kem_polynomial_add_error_reduce_96(self, error);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_vector_u_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    result[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          libcrux_ml_kem_polynomial_ntt_multiply_ef_96(a_element, &r_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_ef_1b(&result[i1],
                                                          &product);
    }
    libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(&result[i1]);
    libcrux_ml_kem_polynomial_add_error_reduce_ef_96(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_compress_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10, (uint16_t)a.elements[i0]);
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_2c
with const generics
- COEFFICIENT_BITS= 10
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_2c_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_compress_ef(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_10_ff(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_compress_2c_ef(
            libcrux_ml_kem_serialize_to_unsigned_field_modulus_96(
                re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_portable_serialize_10_2c(coefficient, bytes);
    Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
        serialized, (size_t)20U * i0, (size_t)20U * i0 + (size_t)20U, uint8_t);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)20U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_fe(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  libcrux_ml_kem_serialize_compress_then_serialize_10_ff(re, uu____0);
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_compress_then_serialize_u_43(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t);
    uint8_t ret[320U];
    libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_fe(&re,
                                                                       ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_ed libcrux_ml_kem_ind_cpa_encrypt_c1_85(
    Eurydice_slice randomness,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix)[3U],
    Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    r_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  uint8_t domain_separator0 =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_3b(r_as_ntt, prf_input,
                                                           0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_1[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    error_1[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  uint8_t domain_separator = libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_3b(
      prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  libcrux_ml_kem_hash_functions_portable_PRF_f1_410(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t), prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u[3U];
  libcrux_ml_kem_matrix_compute_vector_u_1b(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  memcpy(
      uu____0, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_compress_then_serialize_u_43(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d copy_of_r_as_ntt[3U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  tuple_ed lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  lit.snd = error_2;
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_traits_decompress_1_96(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector z =
      libcrux_ml_kem_vector_portable_ZERO_2c();
  libcrux_ml_kem_vector_portable_vector_type_PortableVector s =
      libcrux_ml_kem_vector_portable_sub_2c(z, &vec);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector res =
      libcrux_ml_kem_vector_portable_bitwise_and_with_constant_2c(
          s, (int16_t)1665);
  return res;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_serialize_deserialize_then_decompress_message_96(
    uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_compressed =
            libcrux_ml_kem_vector_portable_deserialize_1_2c(
                Eurydice_array_to_subslice2(serialized, (size_t)2U * i0,
                                            (size_t)2U * i0 + (size_t)2U,
                                            uint8_t));
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_traits_decompress_1_96(coefficient_compressed);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_add_message_error_reduce_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(
                result.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector tmp =
        libcrux_ml_kem_vector_portable_add_2c(myself->coefficients[i0],
                                              &message->coefficients[i0]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector tmp0 =
        libcrux_ml_kem_vector_portable_add_2c(coefficient_normal_form, &tmp);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_2c(tmp0);
    result.coefficients[i0] = uu____0;
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_add_message_error_reduce_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d result) {
  return libcrux_ml_kem_polynomial_add_message_error_reduce_96(self, message,
                                                               result);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_matrix_compute_ring_element_v_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result =
      libcrux_ml_kem_polynomial_ZERO_ef_96();
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
        libcrux_ml_kem_polynomial_ntt_multiply_ef_96(&t_as_ntt[i0],
                                                     &r_as_ntt[i0]);
    libcrux_ml_kem_polynomial_add_to_ring_element_ef_1b(&result, &product);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(&result);
  return libcrux_ml_kem_polynomial_add_message_error_reduce_ef_96(
      error_2, message, result);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_compress_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4, (uint16_t)a.elements[i0]);
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_2c
with const generics
- COEFFICIENT_BITS= 4
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_2c_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_compress_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_4_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_compress_2c_d1(
            libcrux_ml_kem_serialize_to_unsigned_field_modulus_96(
                re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_portable_serialize_4_2c(coefficient, bytes);
    Eurydice_slice_copy(
        Eurydice_slice_subslice2(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, Eurydice_slice out) {
  libcrux_ml_kem_serialize_compress_then_serialize_4_96(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_c2_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message_as_ring_element =
      libcrux_ml_kem_serialize_deserialize_then_decompress_message_96(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      libcrux_ml_kem_matrix_compute_ring_element_v_1b(
          t_as_ntt, r_as_ntt, error_2, &message_as_ring_element);
  libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_6c(
      v, ciphertext);
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
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
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_unpacked_2a(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t *message, Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t ciphertext[1088U] = {0U};
  Eurydice_slice uu____0 = randomness;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[3U] =
      public_key->A;
  tuple_ed uu____2 = libcrux_ml_kem_ind_cpa_encrypt_c1_85(
      uu____0, uu____1,
      Eurydice_array_to_subslice2(ciphertext, (size_t)0U, (size_t)960U,
                                  uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____2.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 = uu____2.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____3 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____4 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____5 = &error_2;
  uint8_t *uu____6 = message;
  libcrux_ml_kem_ind_cpa_encrypt_c2_6c(
      uu____3, uu____4, uu____5, uu____6,
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, __builtin_slice_t));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
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
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_2a(
    Eurydice_slice public_key, uint8_t *message, Eurydice_slice randomness,
    uint8_t ret[1088U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key =
          libcrux_ml_kem_ind_cpa_build_unpacked_public_key_3f(public_key);
  uint8_t ret0[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_2a(&unpacked_public_key, message,
                                             randomness, ret0);
  memcpy(ret, ret0, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_d8
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_kdf_d8_d6(
    Eurydice_slice shared_secret, uint8_t *_, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
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
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_decapsulate_62(
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
  libcrux_ml_kem_ind_cpa_decrypt_42(ind_cpa_secret_key, ciphertext->value,
                                    decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, __builtin_slice_t),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_portable_G_f1_e0(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
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
      uint8_t, size_t, __builtin_slice_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_43_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  libcrux_ml_kem_hash_functions_portable_PRF_f1_41(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_2a(ind_cpa_public_key, decrypted,
                                    pseudorandomness, expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_variant_kdf_d8_d6(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret0,
                              uint8_t),
      libcrux_ml_kem_types_as_slice_d4_80(ciphertext),
      implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  libcrux_ml_kem_variant_kdf_d8_d6(
      shared_secret0, libcrux_ml_kem_types_as_slice_d4_80(ciphertext),
      shared_secret);
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
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics
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
static inline void
libcrux_ml_kem_ind_cca_instantiations_portable_decapsulate_35(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_62(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
static inline void libcrux_ml_kem_mlkem768_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_portable_decapsulate_35(
      private_key, ciphertext, ret);
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_d8
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_entropy_preprocess_d8_9c(
    Eurydice_slice randomness, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.H_f1
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_H_f1_e0(
    Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_portable_H(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
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
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_encapsulate_ca(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  libcrux_ml_kem_variant_entropy_preprocess_d8_9c(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, __builtin_slice_t);
  uint8_t ret0[32U];
  libcrux_ml_kem_hash_functions_portable_H_f1_e0(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_fd_d0(public_key),
                              uint8_t),
      ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_portable_G_f1_e0(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_2a(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_fd_d0(public_key),
                              uint8_t),
      randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = libcrux_ml_kem_types_from_00_80(copy_of_ciphertext);
  uint8_t ret[32U];
  libcrux_ml_kem_variant_kdf_d8_d6(shared_secret, ciphertext, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics
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
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_portable_encapsulate_cd(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_ca(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
static inline tuple_c2 libcrux_ml_kem_mlkem768_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t randomness[32U]) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_encapsulate_cd(
      public_key, randomness);
}

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_1a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_default_1a_1b(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {(libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem)}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_d8
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_cpa_keygen_seed_d8_9c(
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
  libcrux_ml_kem_hash_functions_portable_G_f1_e0(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.to_standard_domain
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_traits_to_standard_domain_96(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v) {
  return libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_2c(
      v, LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_traits_to_standard_domain_96(
                myself->coefficients[j]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_2c(
            libcrux_ml_kem_vector_portable_add_2c(coefficient_normal_form,
                                                  &error->coefficients[j]));
    myself->coefficients[j] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_ef_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  libcrux_ml_kem_polynomial_add_standard_error_reduce_96(self, error);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_As_plus_e_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        libcrux_ml_kem_polynomial_ZERO_ef_96();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          libcrux_ml_kem_polynomial_ntt_multiply_ef_96(matrix_element,
                                                       &s_as_ntt[j]);
      libcrux_ml_kem_polynomial_add_to_ring_element_ef_1b(&t_as_ntt[i0],
                                                          &product);
    }
    libcrux_ml_kem_polynomial_add_standard_error_reduce_ef_96(
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_1c(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  libcrux_ml_kem_variant_cpa_keygen_seed_d8_9c(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_2b(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_3b(
          private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    error_as_ntt[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  LowStar_Ignore_ignore(libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_3b(
                            error_as_ntt, prf_input, domain_separator),
                        uint8_t, void *);
  libcrux_ml_kem_matrix_compute_As_plus_e_1b(
      public_key->t_as_ntt, public_key->A, private_key->secret_as_ntt,
      error_as_ntt);
  uint8_t uu____2[32U];
  Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           TryFromSliceError);
  unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_serialize_to_unsigned_field_modulus_96(
            re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_portable_serialize_12_2c(coefficient, bytes);
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_vector_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t);
    uint8_t ret[384U];
    libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_96(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 = t_as_ntt;
  libcrux_ml_kem_ind_cpa_serialize_vector_1b(
      uu____0,
      Eurydice_array_to_subslice2(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1184U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, __builtin_slice_t),
      seed_for_a, uint8_t);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(t_as_ntt, seed_for_a,
                                                     public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static inline libcrux_ml_kem_utils_extraction_helper_Keypair768
libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_6c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key) {
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_89(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U] = {0U};
  libcrux_ml_kem_ind_cpa_serialize_vector_1b(
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair768
libcrux_ml_kem_ind_cpa_generate_keypair_ea(Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 private_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_1a_1b();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 public_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_8d_1b();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_1c(
      key_generation_seed, &private_key, &public_key);
  return libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_6c(&public_key,
                                                                 &private_key);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
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
  libcrux_ml_kem_hash_functions_portable_H_f1_e0(public_key, ret);
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
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_d6(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      private_key, public_key, implicit_rejection_value, out);
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
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_15(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, __builtin_slice_t);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      libcrux_ml_kem_ind_cpa_generate_keypair_ea(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_d6(
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
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_portable_generate_keypair_ce(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_15(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_portable_generate_key_pair(uint8_t randomness[64U]) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_generate_keypair_ce(
      randomness);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_only_d6(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U];
  libcrux_ml_kem_hash_functions_portable_H_f1_e0(
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
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_37(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_d6(private_key);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_portable_validate_private_key_31(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_37(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
static inline bool libcrux_ml_kem_mlkem768_portable_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_validate_private_key_31(
      private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key_only with
const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_portable_validate_private_key_only_41(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_d6(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
static inline bool libcrux_ml_kem_mlkem768_portable_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_validate_private_key_only_41(
      private_key);
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_out_1b(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    deserialized_pk[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_public_key_89(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[3U];
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_out_1b(
      Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, __builtin_slice_t),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_89(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, __builtin_slice_t),
      public_key_serialized);
  return core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq(
      (size_t)1184U, public_key, public_key_serialized, uint8_t, uint8_t, bool);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_portable_validate_public_key_41(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_89(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
static inline bool libcrux_ml_kem_mlkem768_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_validate_public_key_41(
      public_key->value);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0;

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768PublicKeyUnpacked;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0;

typedef struct
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 public_key;
} libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
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
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_decapsulate_51(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_42(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, __builtin_slice_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  libcrux_ml_kem_hash_functions_portable_G_f1_e0(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, __builtin_slice_t);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_43_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  libcrux_ml_kem_hash_functions_portable_PRF_f1_41(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      implicit_rejection_shared_secret);
  uint8_t expected_ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_2a(
      &key_pair->public_key.ind_cpa_public_key, decrypted, pseudorandomness,
      expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_43_80(ciphertext),
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
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.decapsulate with const
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
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_decapsulate_35(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_51(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
static inline void libcrux_ml_kem_mlkem768_portable_unpacked_decapsulate(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_decapsulate_35(
      private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static inline void libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_9c(
    Eurydice_slice randomness, Eurydice_slice pk_hash, uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, __builtin_slice_t),
      pk_hash, uint8_t);
  uint8_t ret0[64U];
  libcrux_ml_kem_hash_functions_portable_G_f1_e0(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
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
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_9c(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, public_key->public_key_hash,
                              uint8_t),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  uint8_t ciphertext[1088U];
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_2a(&public_key->ind_cpa_public_key,
                                             randomness, pseudorandomness,
                                             ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 =
      libcrux_ml_kem_types_from_00_80(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.encapsulate with const
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
static KRML_MUSTINLINE tuple_c2
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_encapsulate_cd(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
static inline tuple_c2 libcrux_ml_kem_mlkem768_portable_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_encapsulate_cd(
      public_key, randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline void libcrux_ml_kem_ind_cca_unpacked_transpose_a_closure_1b(
    size_t _i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    ret[i] = libcrux_ml_kem_polynomial_ZERO_ef_96();
  }
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2])}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_8d
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_clone_8d_96(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector ret[16U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)16U, self->coefficients, ret,
      libcrux_ml_kem_vector_portable_vector_type_PortableVector, void *);
  memcpy(lit.coefficients, ret,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline void libcrux_ml_kem_ind_cca_unpacked_transpose_a_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ind_cpa_a[3U][3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[3U][3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    libcrux_ml_kem_ind_cca_unpacked_transpose_a_closure_1b(i, A[i]);
  }
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d _a_i[3U][3U];
    memcpy(_a_i, A,
           (size_t)3U *
               sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
    for (size_t i1 = (size_t)0U; i1 < (size_t)3U; i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          libcrux_ml_kem_polynomial_clone_8d_96(&ind_cpa_a[j][i0]);
      A[i0][j] = uu____0;
    }
  }
  memcpy(ret, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_15(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice2(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, __builtin_slice_t);
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_1c(
      ind_cpa_keypair_randomness, &out->private_key.ind_cpa_private_key,
      &out->public_key.ind_cpa_public_key);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U][3U];
  memcpy(uu____0, out->public_key.ind_cpa_public_key.A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[3U][3U];
  libcrux_ml_kem_ind_cca_unpacked_transpose_a_1b(uu____0, A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____1[3U][3U];
  memcpy(uu____1, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  memcpy(out->public_key.ind_cpa_public_key.A, uu____1,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  uint8_t pk_serialized[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_89(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      pk_serialized);
  uint8_t uu____2[32U];
  libcrux_ml_kem_hash_functions_portable_H_f1_e0(
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t), uu____2);
  memcpy(out->public_key.public_key_hash, uu____2,
         (size_t)32U * sizeof(uint8_t));
  uint8_t uu____3[32U];
  Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], TryFromSliceError);
  unwrap_26_b3(dst, uu____3);
  memcpy(out->private_key.implicit_rejection_value, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.generate_keypair with
const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_generate_keypair_ce(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_15(copy_of_randomness, out);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair_mut(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_generate_keypair_ce(
      copy_of_randomness, key_pair);
}

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_09
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_default_09_1b(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_8d_1b();
  uint8_t repeat_expression[32U] = {0U};
  memcpy(lit.public_key_hash, repeat_expression, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1])#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_53
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
    libcrux_ml_kem_ind_cca_unpacked_default_53_1b(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____0;
  uu____0.ind_cpa_private_key = libcrux_ml_kem_ind_cpa_unpacked_default_1a_1b();
  uint8_t repeat_expression[32U] = {0U};
  memcpy(uu____0.implicit_rejection_value, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  return (libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked{
      uu____0, libcrux_ml_kem_ind_cca_unpacked_default_09_1b()});
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
static inline libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair(
    uint8_t randomness[64U]) {
  libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_53_1b();
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair_mut(uu____0,
                                                                  &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
static inline libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_portable_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_53_1b();
}

/**
 Create a new, empty unpacked public key.
*/
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_mlkem768_portable_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_09_1b();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_42(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  libcrux_ml_kem_ind_cpa_deserialize_vector_1b(
      ind_cpa_secret_key,
      key_pair->private_key.ind_cpa_private_key.secret_as_ntt);
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_3f(
      ind_cpa_public_key, &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A, uint8_t);
  Eurydice_slice_copy(
      uu____1,
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1152U, uint8_t,
                                   size_t, __builtin_slice_t),
      uint8_t);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.keypair_from_private_key
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_keypair_from_private_key_fd(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_42(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_from_private_mut(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_keypair_from_private_key_fd(
      private_key, key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_fc with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_fc_43(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_6c(
          &self->public_key.ind_cpa_public_key,
          &self->private_key.ind_cpa_private_key);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t ind_cpa_public_key[1184U];
  memcpy(ind_cpa_public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_fc with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_fc_43(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk =
      libcrux_ml_kem_types_default_24_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_fc_43(self, &sk);
  return sk;
}

/**
 Get the serialized private key.
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_fc_43(key_pair);
}

/**
 Get the serialized private key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_fc_43(key_pair,
                                                                   serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_30
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_30_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  uint8_t ret[1184U];
  libcrux_ml_kem_ind_cpa_serialize_public_key_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      ret);
  return libcrux_ml_kem_types_from_5f_d0(ret);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_fc with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_fc_89(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_30_89(&self->public_key);
}

/**
 Get the serialized public key.
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_fc_89(key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_30
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_30_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_fc with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_fc_89(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_30_89(&self->public_key,
                                                       serialized);
}

/**
 Get the serialized public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_fc_89(key_pair,
                                                                  serialized);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2])#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_ef
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_clone_ef_1b(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)3U, self->t_as_ntt, uu____0,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d, void *);
  uint8_t uu____1[32U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)32U, self->seed_for_A, uu____1, uint8_t, void *);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U][3U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)3U, self->A, ret,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U], void *);
  memcpy(lit.A, ret,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  return lit;
}

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2])#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_clone_dd_1b(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key =
      libcrux_ml_kem_ind_cpa_unpacked_clone_ef_1b(&self->ind_cpa_public_key);
  uint8_t ret[32U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)32U, self->public_key_hash, ret, uint8_t, void *);
  memcpy(lit.public_key_hash, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_fc
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *
libcrux_ml_kem_ind_cca_unpacked_public_key_fc_1b(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
 Get the unpacked public key.
*/
static inline void libcrux_ml_kem_mlkem768_portable_unpacked_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *pk) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 uu____0 =
      libcrux_ml_kem_ind_cca_unpacked_clone_dd_1b(
          libcrux_ml_kem_ind_cca_unpacked_public_key_fc_1b(key_pair));
  pk[0U] = uu____0;
}

/**
 Get the serialized public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_30_89(public_key, serialized);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_0a(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key->value, (size_t)1152U, uint8_t, size_t,
      __builtin_slice_t);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      uu____0, unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      __builtin_slice_t),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____2)[3U] =
      unpacked_public_key->ind_cpa_public_key.A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      __builtin_slice_t),
      ret);
  libcrux_ml_kem_matrix_sample_matrix_A_2b(uu____2, ret, false);
  uint8_t uu____3[32U];
  libcrux_ml_kem_hash_functions_portable_H_f1_e0(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_fd_d0(public_key),
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
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.unpack_public_key with
const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_unpack_public_key_31(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_0a(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_unpacked_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_unpack_public_key_31(
      public_key, unpacked_public_key);
}

#define __libcrux_mlkem768_portable_H_DEFINED
#endif
