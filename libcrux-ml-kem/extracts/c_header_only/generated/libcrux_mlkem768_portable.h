/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: unset
 * Libcrux: bccb526ae5d7c8a8845745889b8996dfe9917915
 */

#ifndef libcrux_mlkem768_portable_H
#define libcrux_mlkem768_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_ct_ops.h"
#include "libcrux_mlkem_core.h"
#include "libcrux_sha3_portable.h"

static inline void libcrux_ml_kem_hash_functions_portable_G(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_sha3_portable_sha512(output, input);
}

static inline void libcrux_ml_kem_hash_functions_portable_H(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_sha3_portable_sha256(output, input);
}

static inline void libcrux_ml_kem_hash_functions_portable_PRFxN(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, uint8_t[33U]);
       i++) {
    size_t i0 = i;
    libcrux_sha3_portable_shake256(
        Eurydice_slice_subslice3(outputs, i0 * out_len,
                                 (i0 + (size_t)1U) * out_len, uint8_t *),
        Eurydice_array_to_slice(
            (size_t)33U,
            Eurydice_slice_index(input, i0, uint8_t[33U], uint8_t(*)[33U]),
            uint8_t));
  }
}

typedef struct libcrux_ml_kem_hash_functions_portable_PortableHash_s {
  libcrux_sha3_generic_keccak_KeccakState_17 shake128_state[4U];
} libcrux_ml_kem_hash_functions_portable_PortableHash;

static inline libcrux_ml_kem_hash_functions_portable_PortableHash
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_slice input) {
  libcrux_sha3_generic_keccak_KeccakState_17 shake128_state[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    shake128_state[i] = libcrux_sha3_portable_incremental_shake128_init();
  }
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(input, uint8_t[34U]);
       i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_absorb_final(
        &shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)34U,
            Eurydice_slice_index(input, i0, uint8_t[34U], uint8_t(*)[34U]),
            uint8_t));
  }
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_sha3_generic_keccak_KeccakState_17 copy_of_shake128_state[4U];
  memcpy(copy_of_shake128_state, shake128_state,
         (size_t)4U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  libcrux_ml_kem_hash_functions_portable_PortableHash lit;
  memcpy(lit.shake128_state, copy_of_shake128_state,
         (size_t)4U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  return lit;
}

static inline void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    libcrux_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(outputs, uint8_t[504U]);
       i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
        &st->shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)504U,
            Eurydice_slice_index(outputs, i0, uint8_t[504U], uint8_t(*)[504U]),
            uint8_t));
  }
}

static inline void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    libcrux_ml_kem_hash_functions_portable_PortableHash *st,
    Eurydice_slice outputs) {
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(outputs, uint8_t[168U]);
       i++) {
    size_t i0 = i;
    libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
        &st->shake128_state[i0],
        Eurydice_array_to_slice(
            (size_t)168U,
            Eurydice_slice_index(outputs, i0, uint8_t[168U], uint8_t(*)[168U]),
            uint8_t));
  }
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static inline void libcrux_ml_kem_hash_functions_portable_G_6e(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_portable_G(input, output);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static inline void libcrux_ml_kem_hash_functions_portable_H_6e(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_portable_H(input, output);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static inline void libcrux_ml_kem_hash_functions_portable_PRFxN_6e(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  libcrux_ml_kem_hash_functions_portable_PRFxN(input, outputs, out_len);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_6e(
    Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final(
      input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_6e(
    libcrux_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
      self, output);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_6e(
    libcrux_ml_kem_hash_functions_portable_PortableHash *self,
    Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block(self,
                                                                     output);
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

#define LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT ((size_t)16U)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS \
  ((int16_t)1353)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS ((int16_t)3329)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (62209U)

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_s {
  int16_t elements[16U];
} libcrux_ml_kem_vector_portable_vector_type_PortableVector;

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_zero(void) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  int16_t ret[16U];
  int16_t buf[16U] = {0U};
  libcrux_secrets_int_public_integers_classify_27_46(buf, ret);
  memcpy(lit.elements, ret, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ZERO_b8(void) {
  return libcrux_ml_kem_vector_portable_vector_type_zero();
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)16U, out->elements, int16_t),
      Eurydice_slice_subslice3(array, (size_t)0U, (size_t)16U, int16_t *),
      int16_t);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_from_i16_array_b8(
    Eurydice_slice array,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
      libcrux_secrets_int_classify_public_classify_ref_9b_39(array), out);
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

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_arithmetic_add(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->elements[uu____0] = lhs->elements[uu____0] + rhs->elements[i0];
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_add_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  libcrux_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_arithmetic_sub(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->elements[uu____0] = lhs->elements[uu____0] - rhs->elements[i0];
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_sub_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  libcrux_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_arithmetic_negate(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec->elements[i0] = -vec->elements[i0];
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_negate_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_ml_kem_vector_portable_arithmetic_negate(vec);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->elements[uu____0] = vec->elements[uu____0] * c;
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_multiply_by_constant_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t c) {
  libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->elements[uu____0] = vec->elements[uu____0] & c;
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_bitwise_and_with_constant_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t c) {
  libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(vec, c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (libcrux_secrets_int_public_integers_declassify_d8_39(
            vec->elements[i0]) >= (int16_t)3329) {
      size_t uu____0 = i0;
      vec->elements[uu____0] = vec->elements[uu____0] - (int16_t)3329;
    }
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(vec);
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
  int32_t t = libcrux_secrets_int_as_i32_f5(value) *
                  LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER +
              (LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient = libcrux_secrets_int_as_i16_36(
      t >> (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  return value - quotient * LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec->elements[i0]);
    vec->elements[i0] = vi;
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_barrett_reduce_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(vec);
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
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(value)) *
      libcrux_secrets_int_as_i32_b8(
          libcrux_secrets_int_public_integers_classify_27_df(
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  int32_t k_times_modulus =
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(k)) *
      libcrux_secrets_int_as_i32_f5(
          libcrux_secrets_int_public_integers_classify_27_39(
              LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  int16_t c = libcrux_secrets_int_as_i16_36(
      k_times_modulus >>
      (uint32_t)LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high = libcrux_secrets_int_as_i16_36(
      value >>
      (uint32_t)LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
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
  int32_t product =
      libcrux_secrets_int_as_i32_f5(fe) * libcrux_secrets_int_as_i32_f5(fer);
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec->elements[i0] =
        libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec->elements[i0], c);
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec, int16_t r) {
  libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vec, libcrux_secrets_int_public_integers_classify_27_39(r));
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_clone_9c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *self) {
  return self[0U];
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_arithmetic_shift_right_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->elements[uu____0] = vec->elements[uu____0] >> (uint32_t)(int32_t)15;
  }
}

static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
      libcrux_ml_kem_vector_portable_vector_type_clone_9c(&a);
  libcrux_ml_kem_vector_portable_arithmetic_shift_right_ef(&t);
  libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
      &t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  libcrux_ml_kem_vector_portable_arithmetic_add(&a, &t);
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(
      a);
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
  int16_t shifted =
      libcrux_secrets_int_public_integers_classify_27_39((int16_t)1664) -
      libcrux_secrets_int_as_i16_ca(fe);
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range = shifted_to_positive - (int16_t)832;
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & (int16_t)1;
  return libcrux_secrets_int_as_u8_f5(r1);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_compress_compress_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    a->elements[i0] = libcrux_secrets_int_as_i16_59(
        libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
            libcrux_secrets_int_as_u16_f5(a->elements[i0])));
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_compress_1_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_ml_kem_vector_portable_compress_compress_1(a);
}

static KRML_MUSTINLINE uint32_t
libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  return value & ((1U << (uint32_t)n) - 1U);
}

static inline int16_t
libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = libcrux_secrets_int_as_u64_ca(fe)
                        << (uint32_t)coefficient_bits;
  compressed = compressed + 1664ULL;
  compressed = compressed * 10321340ULL;
  compressed = compressed >> 35U;
  return libcrux_secrets_int_as_i16_b8(
      libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, libcrux_secrets_int_as_u32_a3(compressed)));
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->elements[j],
          libcrux_secrets_int_public_integers_classify_27_39(zeta));
  int16_t a_minus_t = vec->elements[i] - t;
  int16_t a_plus_t = vec->elements[i] + t;
  vec->elements[j] = a_minus_t;
  vec->elements[i] = a_plus_t;
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                              (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                              (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)4U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)5U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)8U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)9U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)12U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)13U,
                                              (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1, zeta2,
                                                      zeta3);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                              (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                              (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)2U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)3U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)8U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)9U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)10U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)11U,
                                              (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a, int16_t zeta0,
    int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)0U,
                                              (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)1U,
                                              (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)2U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)3U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)4U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)5U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)6U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)7U,
                                              (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
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
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_39(zeta));
  vec->elements[i] = o0;
  vec->elements[j] = o1;
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)4U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)5U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)8U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)9U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)12U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)13U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(a, zeta0, zeta1,
                                                          zeta2, zeta3);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)2U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)3U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)8U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)9U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)10U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)11U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a, int16_t zeta0,
    int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0, zeta1);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)0U,
                                                  (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)1U,
                                                  (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)2U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)3U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)4U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)5U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)6U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)7U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
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
  int32_t ai_bi =
      libcrux_secrets_int_as_i32_f5(ai) * libcrux_secrets_int_as_i32_f5(bi);
  int32_t aj_bj_ =
      libcrux_secrets_int_as_i32_f5(aj) * libcrux_secrets_int_as_i32_f5(bj);
  int16_t aj_bj =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          aj_bj_);
  int32_t aj_bj_zeta = libcrux_secrets_int_as_i32_f5(aj_bj) *
                       libcrux_secrets_int_as_i32_f5(zeta);
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int16_t o0 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bi_aj_bj);
  int32_t ai_bj =
      libcrux_secrets_int_as_i32_f5(ai) * libcrux_secrets_int_as_i32_f5(bj);
  int32_t aj_bi =
      libcrux_secrets_int_as_i32_f5(aj) * libcrux_secrets_int_as_i32_f5(bi);
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bj_aj_bi);
  out->elements[(size_t)2U * i] = o0;
  out->elements[(size_t)2U * i + (size_t)1U] = o1;
}

static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_ntt_multiply_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply(lhs, rhs, out, zeta0, zeta1,
                                                  zeta2, zeta3);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) =
      libcrux_secrets_int_public_integers_declassify_d8_90(
          (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[0U]) |
                (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[1U]) << 1U) |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[2U]) << 2U) |
              (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[3U]) << 3U) |
             (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[4U]) << 4U) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[5U]) << 5U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[6U]) << 6U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[7U]) << 7U);
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) =
      libcrux_secrets_int_public_integers_declassify_d8_90(
          (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[8U]) |
                (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[9U]) << 1U) |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[10U]) << 2U) |
              (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[11U]) << 3U) |
             (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[12U]) << 4U) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[13U]) << 5U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[14U]) << 6U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->elements[15U]) << 7U);
}

static inline void libcrux_ml_kem_vector_portable_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_serialize_1(a, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_1_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_1(a, out);
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_slice v,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  out->elements[0U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) & 1U);
  out->elements[1U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 1U &
      1U);
  out->elements[2U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 2U &
      1U);
  out->elements[3U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 3U &
      1U);
  out->elements[4U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 4U &
      1U);
  out->elements[5U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 5U &
      1U);
  out->elements[6U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 6U &
      1U);
  out->elements[7U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 7U &
      1U);
  out->elements[8U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) & 1U);
  out->elements[9U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 1U &
      1U);
  out->elements[10U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 2U &
      1U);
  out->elements[11U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 3U &
      1U);
  out->elements[12U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 4U &
      1U);
  out->elements[13U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 5U &
      1U);
  out->elements[14U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 6U &
      1U);
  out->elements[15U] = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 7U &
      1U);
}

static inline void libcrux_ml_kem_vector_portable_deserialize_1(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_serialize_deserialize_1(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_deserialize_1_b8(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_deserialize_1(a, out);
}

typedef struct uint8_t_x4_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
} uint8_t_x4;

static KRML_MUSTINLINE uint8_t_x4
libcrux_ml_kem_vector_portable_serialize_serialize_4_int(Eurydice_slice v) {
  uint8_t result0 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)0U, int16_t, int16_t *));
  uint8_t result1 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)2U, int16_t, int16_t *));
  uint8_t result2 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)4U, int16_t, int16_t *));
  uint8_t result3 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)6U, int16_t, int16_t *));
  return (KRML_CLITERAL(uint8_t_x4){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(result0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(result1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(result2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(result3)});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x4 uu____0 = libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
      Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)8U,
                                  int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  uint8_t_x4 uu____4 = libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
      Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)16U,
                                  int16_t *));
  uint8_t uu____5 = uu____4.snd;
  uint8_t uu____6 = uu____4.thd;
  uint8_t uu____7 = uu____4.f3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4.fst;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
}

static inline void libcrux_ml_kem_vector_portable_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_serialize_4(a, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_4_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_4(a, out);
}

static KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) &
      15U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
      15U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
      15U);
  int16_t v5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) &
      15U);
  int16_t v7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          4U &
      15U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_deserialize_4(
    Eurydice_slice bytes,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)4U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)8U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

static inline void libcrux_ml_kem_vector_portable_deserialize_4(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_serialize_deserialize_4(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_deserialize_4_b8(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_deserialize_4(a, out);
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
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) & (int16_t)255);
  uint8_t r1 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) & (int16_t)63)
          << 2U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U &
          (int16_t)3);
  uint8_t r2 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) & (int16_t)15)
          << 4U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 6U &
          (int16_t)15);
  uint8_t r3 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) & (int16_t)3)
          << 6U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) >> 4U &
          (int16_t)63);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 2U &
      (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4)});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x5 uu____0 =
      libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)4U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)4U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5.fst;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9;
  uint8_t_x5 uu____10 =
      libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)12U,
                                      int16_t *));
  uint8_t uu____11 = uu____10.snd;
  uint8_t uu____12 = uu____10.thd;
  uint8_t uu____13 = uu____10.f3;
  uint8_t uu____14 = uu____10.f4;
  Eurydice_slice_index(out, (size_t)10U, uint8_t, uint8_t *) = uu____10.fst;
  Eurydice_slice_index(out, (size_t)11U, uint8_t, uint8_t *) = uu____11;
  Eurydice_slice_index(out, (size_t)12U, uint8_t, uint8_t *) = uu____12;
  Eurydice_slice_index(out, (size_t)13U, uint8_t, uint8_t *) = uu____13;
  Eurydice_slice_index(out, (size_t)14U, uint8_t, uint8_t *) = uu____14;
  uint8_t_x5 uu____15 =
      libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)12U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  uint8_t uu____18 = uu____15.f3;
  uint8_t uu____19 = uu____15.f4;
  Eurydice_slice_index(out, (size_t)15U, uint8_t, uint8_t *) = uu____15.fst;
  Eurydice_slice_index(out, (size_t)16U, uint8_t, uint8_t *) = uu____16;
  Eurydice_slice_index(out, (size_t)17U, uint8_t, uint8_t *) = uu____17;
  Eurydice_slice_index(out, (size_t)18U, uint8_t, uint8_t *) = uu____18;
  Eurydice_slice_index(out, (size_t)19U, uint8_t, uint8_t *) = uu____19;
}

static inline void libcrux_ml_kem_vector_portable_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_serialize_10(a, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_10_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_10(a, out);
}

static KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes) {
  int16_t r0 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *)) &
       (int16_t)255));
  int16_t r1 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)) >>
          2U);
  int16_t r2 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)) >>
          4U);
  int16_t r3 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)) >>
          6U);
  int16_t r4 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *)) &
       (int16_t)255));
  int16_t r5 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *)) >>
          2U);
  int16_t r6 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)) >>
          4U);
  int16_t r7 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *)) >>
          6U);
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_deserialize_10(
    Eurydice_slice bytes,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x8 uu____0 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)10U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  out->elements[2U] = uu____2;
  out->elements[3U] = uu____3;
  out->elements[4U] = uu____4;
  out->elements[5U] = uu____5;
  out->elements[6U] = uu____6;
  out->elements[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)10U, (size_t)20U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  out->elements[10U] = uu____10;
  out->elements[11U] = uu____11;
  out->elements[12U] = uu____12;
  out->elements[13U] = uu____13;
  out->elements[14U] = uu____14;
  out->elements[15U] = uu____15;
}

static inline void libcrux_ml_kem_vector_portable_deserialize_10(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_serialize_deserialize_10(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_deserialize_10_b8(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_deserialize_10(a, out);
}

typedef struct uint8_t_x3_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
} uint8_t_x3;

static KRML_MUSTINLINE uint8_t_x3
libcrux_ml_kem_vector_portable_serialize_serialize_12_int(Eurydice_slice v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) & (int16_t)255);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U |
      (Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) & (int16_t)15)
          << 4U);
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 4U &
      (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x3){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2)});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v,
    Eurydice_slice out) {
  uint8_t_x3 uu____0 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)0U, (size_t)2U,
                                      int16_t *));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) = uu____0.fst;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) = uu____1;
  Eurydice_slice_index(out, (size_t)2U, uint8_t, uint8_t *) = uu____2;
  uint8_t_x3 uu____3 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)2U, (size_t)4U,
                                      int16_t *));
  uint8_t uu____4 = uu____3.snd;
  uint8_t uu____5 = uu____3.thd;
  Eurydice_slice_index(out, (size_t)3U, uint8_t, uint8_t *) = uu____3.fst;
  Eurydice_slice_index(out, (size_t)4U, uint8_t, uint8_t *) = uu____4;
  Eurydice_slice_index(out, (size_t)5U, uint8_t, uint8_t *) = uu____5;
  uint8_t_x3 uu____6 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)4U, (size_t)6U,
                                      int16_t *));
  uint8_t uu____7 = uu____6.snd;
  uint8_t uu____8 = uu____6.thd;
  Eurydice_slice_index(out, (size_t)6U, uint8_t, uint8_t *) = uu____6.fst;
  Eurydice_slice_index(out, (size_t)7U, uint8_t, uint8_t *) = uu____7;
  Eurydice_slice_index(out, (size_t)8U, uint8_t, uint8_t *) = uu____8;
  uint8_t_x3 uu____9 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)6U, (size_t)8U,
                                      int16_t *));
  uint8_t uu____10 = uu____9.snd;
  uint8_t uu____11 = uu____9.thd;
  Eurydice_slice_index(out, (size_t)9U, uint8_t, uint8_t *) = uu____9.fst;
  Eurydice_slice_index(out, (size_t)10U, uint8_t, uint8_t *) = uu____10;
  Eurydice_slice_index(out, (size_t)11U, uint8_t, uint8_t *) = uu____11;
  uint8_t_x3 uu____12 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)8U, (size_t)10U,
                                      int16_t *));
  uint8_t uu____13 = uu____12.snd;
  uint8_t uu____14 = uu____12.thd;
  Eurydice_slice_index(out, (size_t)12U, uint8_t, uint8_t *) = uu____12.fst;
  Eurydice_slice_index(out, (size_t)13U, uint8_t, uint8_t *) = uu____13;
  Eurydice_slice_index(out, (size_t)14U, uint8_t, uint8_t *) = uu____14;
  uint8_t_x3 uu____15 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)10U, (size_t)12U,
                                      int16_t *));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  Eurydice_slice_index(out, (size_t)15U, uint8_t, uint8_t *) = uu____15.fst;
  Eurydice_slice_index(out, (size_t)16U, uint8_t, uint8_t *) = uu____16;
  Eurydice_slice_index(out, (size_t)17U, uint8_t, uint8_t *) = uu____17;
  uint8_t_x3 uu____18 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)12U, (size_t)14U,
                                      int16_t *));
  uint8_t uu____19 = uu____18.snd;
  uint8_t uu____20 = uu____18.thd;
  Eurydice_slice_index(out, (size_t)18U, uint8_t, uint8_t *) = uu____18.fst;
  Eurydice_slice_index(out, (size_t)19U, uint8_t, uint8_t *) = uu____19;
  Eurydice_slice_index(out, (size_t)20U, uint8_t, uint8_t *) = uu____20;
  uint8_t_x3 uu____21 =
      libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice3(v->elements, (size_t)14U, (size_t)16U,
                                      int16_t *));
  uint8_t uu____22 = uu____21.snd;
  uint8_t uu____23 = uu____21.thd;
  Eurydice_slice_index(out, (size_t)21U, uint8_t, uint8_t *) = uu____21.fst;
  Eurydice_slice_index(out, (size_t)22U, uint8_t, uint8_t *) = uu____22;
  Eurydice_slice_index(out, (size_t)23U, uint8_t, uint8_t *) = uu____23;
}

static inline void libcrux_ml_kem_vector_portable_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_serialize_12(a, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_serialize_12_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    Eurydice_slice out) {
  libcrux_ml_kem_vector_portable_serialize_12(a, out);
}

typedef struct int16_t_x2_s {
  int16_t fst;
  int16_t snd;
} int16_t_x2;

static KRML_MUSTINLINE int16_t_x2
libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes) {
  int16_t byte0 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  int16_t byte1 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *));
  int16_t byte2 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *));
  int16_t r0 = (byte1 & (int16_t)15) << 8U | (byte0 & (int16_t)255);
  int16_t r1 = byte2 << 4U | (byte1 >> 4U & (int16_t)15);
  return (KRML_CLITERAL(int16_t_x2){.fst = r0, .snd = r1});
}

static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_slice bytes,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t_x2 uu____0 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)3U, uint8_t *));
  int16_t uu____1 = uu____0.snd;
  out->elements[0U] = uu____0.fst;
  out->elements[1U] = uu____1;
  int16_t_x2 uu____2 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)3U, (size_t)6U, uint8_t *));
  int16_t uu____3 = uu____2.snd;
  out->elements[2U] = uu____2.fst;
  out->elements[3U] = uu____3;
  int16_t_x2 uu____4 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)6U, (size_t)9U, uint8_t *));
  int16_t uu____5 = uu____4.snd;
  out->elements[4U] = uu____4.fst;
  out->elements[5U] = uu____5;
  int16_t_x2 uu____6 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)9U, (size_t)12U, uint8_t *));
  int16_t uu____7 = uu____6.snd;
  out->elements[6U] = uu____6.fst;
  out->elements[7U] = uu____7;
  int16_t_x2 uu____8 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)12U, (size_t)15U, uint8_t *));
  int16_t uu____9 = uu____8.snd;
  out->elements[8U] = uu____8.fst;
  out->elements[9U] = uu____9;
  int16_t_x2 uu____10 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)15U, (size_t)18U, uint8_t *));
  int16_t uu____11 = uu____10.snd;
  out->elements[10U] = uu____10.fst;
  out->elements[11U] = uu____11;
  int16_t_x2 uu____12 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)18U, (size_t)21U, uint8_t *));
  int16_t uu____13 = uu____12.snd;
  out->elements[12U] = uu____12.fst;
  out->elements[13U] = uu____13;
  int16_t_x2 uu____14 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)21U, (size_t)24U, uint8_t *));
  int16_t uu____15 = uu____14.snd;
  out->elements[14U] = uu____14.fst;
  out->elements[15U] = uu____15;
}

static inline void libcrux_ml_kem_vector_portable_deserialize_12(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_serialize_deserialize_12(
      libcrux_secrets_int_classify_public_classify_ref_9b_90(a), out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline void libcrux_ml_kem_vector_portable_deserialize_12_b8(
    Eurydice_slice a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_deserialize_12(a, out);
}

static KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_portable_sampling_rej_sample(Eurydice_slice a,
                                                   Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(a, uint8_t) / (size_t)3U;
       i++) {
    size_t i0 = i;
    int16_t b1 =
        (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U, uint8_t, uint8_t *);
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
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
static inline size_t libcrux_ml_kem_vector_portable_rej_sample_b8(
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

#define LIBCRUX_ML_KEM_MLKEM768_PRF_OUTPUT_SIZE1 \
  (LIBCRUX_ML_KEM_MLKEM768_ETA1_RANDOMNESS_SIZE * LIBCRUX_ML_KEM_MLKEM768_RANK)

#define LIBCRUX_ML_KEM_MLKEM768_PRF_OUTPUT_SIZE2 \
  (LIBCRUX_ML_KEM_MLKEM768_ETA2_RANDOMNESS_SIZE * LIBCRUX_ML_KEM_MLKEM768_RANK)

#define LIBCRUX_ML_KEM_MLKEM768_RANKED_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_MLKEM768_RANK *                             \
   LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_MLKEM768_RANK_SQUARED \
  (LIBCRUX_ML_KEM_MLKEM768_RANK * LIBCRUX_ML_KEM_MLKEM768_RANK)

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
libcrux_ml_kem.polynomial.{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]}.ZERO.{core::ops::function::FnMut<(usize),␣Vector>␣for␣libcrux_ml_kem::polynomial::{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]}::ZERO::closure<Vector>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_polynomial__libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___ZERO__core__ops__function__FnMut__usize___Vector__for_libcrux_ml_kem__polynomial___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1____ZERO__closure_Vector__TraitClause_0__TraitClause_1___call_mut_df(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_vector_portable_ZERO_b8();
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_ZERO_d6_df(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector ret[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_polynomial__libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___ZERO__core__ops__function__FnMut__usize___Vector__for_libcrux_ml_kem__polynomial___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1____ZERO__closure_Vector__TraitClause_0__TraitClause_1___call_mut_df(
            &lvalue, i);
  }
  memcpy(lit.coefficients, ret,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

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
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_decrypt_call_mut_0b_42(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_df(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes,
                                                     &re->coefficients[i0]);
  }
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
    Eurydice_slice secret_key, Eurydice_slice secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_df(
        Eurydice_slice_subslice3(
            secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *),
        &Eurydice_slice_index(
            secret_as_ntt, i0,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
  }
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector,
K, CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked.call_mut_68
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_decrypt_unpacked_call_mut_68_42(void **_,
                                                       size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a->elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a->elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 10
*/
static inline void
libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_b8_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_ef(
      a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_10_df(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    libcrux_ml_kem_vector_portable_deserialize_10_b8(bytes,
                                                     &re->coefficients[i0]);
    libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_b8_ef(
        &re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_0a(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *output) {
  libcrux_ml_kem_serialize_deserialize_then_decompress_10_df(serialized,
                                                             output);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_traits_montgomery_multiply_fe_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v, int16_t fer) {
  libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_layer_int_vec_step_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *coefficients,
    size_t a, size_t b,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    int16_t zeta_r) {
  scratch[0U] = coefficients[b];
  libcrux_ml_kem_vector_traits_montgomery_multiply_fe_df(scratch, zeta_r);
  coefficients[b] = coefficients[a];
  libcrux_ml_kem_vector_portable_add_b8(&coefficients[a], scratch);
  libcrux_ml_kem_vector_portable_sub_b8(&coefficients[b], scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t layer,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    size_t _initial_coefficient_bound) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec = step / (size_t)16U;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_ntt_ntt_layer_int_vec_step_df(
          re->coefficients, a_offset + j, b_offset + j, scratch,
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_3_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_2_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_1_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_barrett_reduce_b8(&myself->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  libcrux_ml_kem_polynomial_poly_barrett_reduce_df(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_vector_u_0a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t zeta_i = (size_t)0U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)7U, scratch,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)6U, scratch,
                                            (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)5U, scratch,
                                            (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)4U, scratch,
                                            (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_df(&zeta_i, re, (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_df(&zeta_i, re, (size_t)6U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_df(&zeta_i, re, (size_t)7U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_df(re);
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
    uint8_t *ciphertext, Eurydice_slice u_as_ntt,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
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
    libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_0a(
        u_bytes,
        &Eurydice_slice_index(
            u_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
    libcrux_ml_kem_ntt_ntt_vector_u_0a(
        &Eurydice_slice_index(
            u_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
        scratch);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a->elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a->elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 4
*/
static inline void
libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_b8_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_ml_kem_vector_portable_compress_decompress_ciphertext_coefficient_d1(
      a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_4_df(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    libcrux_ml_kem_vector_portable_deserialize_4_b8(bytes,
                                                    &re->coefficients[i0]);
    libcrux_ml_kem_vector_portable_decompress_ciphertext_coefficient_b8_d1(
        &re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_89(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *output) {
  libcrux_ml_kem_serialize_deserialize_then_decompress_4_df(serialized, output);
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
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_ntt_multiply_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *out) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_ntt_multiply_b8(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        &out->coefficients[i0],
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)1U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)2U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_ntt_multiply_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *out) {
  libcrux_ml_kem_polynomial_ntt_multiply_df(self, rhs, out);
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
    libcrux_ml_kem_vector_portable_add_b8(&myself->coefficients[i0],
                                          &rhs->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_d6_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  libcrux_ml_kem_polynomial_add_to_ring_element_1b(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *coefficients,
    size_t a, size_t b,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch,
    int16_t zeta_r) {
  scratch->coefficients[0U] = coefficients[a];
  scratch->coefficients[1U] = coefficients[b];
  libcrux_ml_kem_vector_portable_add_b8(&coefficients[a],
                                        &scratch->coefficients[1U]);
  libcrux_ml_kem_vector_portable_sub_b8(&coefficients[b],
                                        scratch->coefficients);
  libcrux_ml_kem_vector_portable_barrett_reduce_b8(&coefficients[a]);
  libcrux_ml_kem_vector_traits_montgomery_multiply_fe_df(&coefficients[b],
                                                         zeta_r);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_df(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t layer, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec =
      step / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_df(
          re->coefficients, a_offset + j, b_offset + j, scratch,
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_df(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_df(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_df(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_df(&zeta_i, re,
                                                          (size_t)4U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_df(&zeta_i, re,
                                                          (size_t)5U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_df(&zeta_i, re,
                                                          (size_t)6U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_df(&zeta_i, re,
                                                          (size_t)7U, scratch);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_df(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_subtract_reduce_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
        &b->coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_portable_sub_b8(&b->coefficients[i0],
                                          &myself->coefficients[i0]);
    libcrux_ml_kem_vector_portable_negate_b8(&b->coefficients[i0]);
    libcrux_ml_kem_vector_portable_barrett_reduce_b8(&b->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_subtract_reduce_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *b) {
  libcrux_ml_kem_polynomial_subtract_reduce_df(self, b);
}

/**
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_message_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *u_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_ntt_multiply_d6_df(&secret_as_ntt[i0],
                                                 &u_as_ntt[i0], scratch);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_1b(result, scratch);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(result, scratch);
  libcrux_ml_kem_polynomial_subtract_reduce_d6_df(v, result);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_to_unsigned_field_modulus_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
      libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(a[0U]);
  out[0U] = uu____0;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_message_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    Eurydice_slice serialized,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_df(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_portable_compress_1_b8(scratch);
    libcrux_ml_kem_vector_portable_serialize_1_b8(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)2U * i0,
                                 (size_t)2U * i0 + (size_t)2U, uint8_t *));
  }
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
    uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    u_as_ntt[i] =
        libcrux_ml_kem_ind_cpa_decrypt_unpacked_call_mut_68_42(&lvalue, i);
  }
  libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_6c(
      ciphertext,
      Eurydice_array_to_slice(
          (size_t)3U, u_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_89(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]),
      &v);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_matrix_compute_message_1b(&v, secret_key->secret_as_ntt,
                                           u_as_ntt, &message, scratch);
  libcrux_ml_kem_serialize_compress_then_serialize_message_df(
      &message, decrypted, scratch->coefficients);
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
    Eurydice_slice secret_key, uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] = libcrux_ml_kem_ind_cpa_decrypt_call_mut_0b_42(&lvalue, i);
  }
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_deserialize_vector_1b(
      secret_key, Eurydice_array_to_slice(
                      (size_t)3U, secret_key_unpacked.secret_as_ntt,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_42(&secret_key_unpacked, ciphertext,
                                             decrypted, scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static inline void libcrux_ml_kem_hash_functions_portable_PRF_9e(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_6e
with const generics
- LEN= 32
*/
static inline void libcrux_ml_kem_hash_functions_portable_PRF_6e_9e(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_portable_PRF_9e(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate.call_mut_5f
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_decapsulate_call_mut_5f_d7(void **_,
                                                  size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
- $9size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[9U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}::default::closure<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_89(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}::default::closure#1<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_1_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_89(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_50
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be
libcrux_ml_kem_ind_cpa_unpacked_default_50_89(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    uu____0[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_89(
            &lvalue, i);
  }
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_1_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_89(
            &lvalue, i);
  }
  memcpy(
      lit.A, ret,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
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
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_df(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes,
                                                     &re->coefficients[i0]);
    libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(&re->coefficients[i0]);
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
    Eurydice_slice public_key, Eurydice_slice deserialized_pk) {
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
    libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_df(
        ring_element,
        &Eurydice_slice_index(
            deserialized_pk, i0,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
  }
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
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i1, uint8_t[504U], uint8_t(*)[504U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
        size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i1;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
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
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i1, uint8_t[168U], uint8_t(*)[168U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
        size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i1;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_57(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_portable_PortableHash xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_6e(
          seeds);
  uint8_t randomness[3U][504U] = {{0U}};
  uint8_t randomness_blocksize[3U][168U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_6e(
      &xof_state,
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]));
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_89(
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_6e(
          &xof_state, Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                              uint8_t[168U]));
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_890(
          Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_from_i16_array_df(
    Eurydice_slice a,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_from_i16_array_b8(
        Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                 (i0 + (size_t)1U) * (size_t)16U, int16_t *),
        &result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_from_i16_array_d6_df(
    Eurydice_slice a, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *out) {
  libcrux_ml_kem_polynomial_from_i16_array_df(a, out);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_57(
    Eurydice_slice A_transpose, uint8_t *seed, bool transpose) {
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
    size_t sampled_coefficients[3U] = {0U};
    int16_t out[3U][272U] = {{0U}};
    libcrux_ml_kem_sampling_sample_from_xof_57(
        Eurydice_array_to_slice((size_t)3U, seeds, uint8_t[34U]),
        Eurydice_array_to_slice((size_t)3U, sampled_coefficients, size_t),
        Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]));
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]),
                 int16_t[272U]);
         i++) {
      size_t j = i;
      int16_t sample[272U];
      memcpy(sample, out[j], (size_t)272U * sizeof(int16_t));
      if (transpose) {
        Eurydice_slice uu____1 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_df(
            uu____1, &Eurydice_slice_index(
                         A_transpose, j * (size_t)3U + i1,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
      } else {
        Eurydice_slice uu____2 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_df(
            uu____2, &Eurydice_slice_index(
                         A_transpose, i1 * (size_t)3U + j,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
      }
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_e2(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, unpacked_public_key->t_as_ntt,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, unpacked_public_key->A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_57(uu____1, ret, false);
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
static KRML_MUSTINLINE void
libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_df(
    Eurydice_slice randomness, Eurydice_slice sampled_i16s) {
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
    for (uint32_t i = 0U; i < 32U / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      Eurydice_slice_index(sampled_i16s, (size_t)8U * chunk_number + offset,
                           int16_t, int16_t *) = outcome_1 - outcome_2;
    }
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
    Eurydice_slice randomness, int16_t *output) {
  libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_df(
      randomness, Eurydice_array_to_slice((size_t)256U, output, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_7_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    scratch[0U] = re->coefficients[j + step];
    libcrux_ml_kem_vector_portable_multiply_by_constant_b8(scratch,
                                                           (int16_t)-1600);
    re->coefficients[j + step] = re->coefficients[j];
    libcrux_ml_kem_vector_portable_add_b8(&re->coefficients[j], scratch);
    libcrux_ml_kem_vector_portable_sub_b8(&re->coefficients[j + step], scratch);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_ntt_ntt_at_layer_7_df(re, scratch);
  size_t zeta_i = (size_t)1U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)6U, scratch,
                                            (size_t)11207U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(&zeta_i, re, (size_t)5U, scratch,
                                            (size_t)11207U + (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_df(
      &zeta_i, re, (size_t)4U, scratch,
      (size_t)11207U + (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_df(
      &zeta_i, re, (size_t)11207U + (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_df(
      &zeta_i, re, (size_t)11207U + (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_df(
      &zeta_i, re, (size_t)11207U + (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_df(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_40(
    Eurydice_slice re_as_ntt, uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  libcrux_ml_kem_hash_functions_portable_PRFxN_6e(
      Eurydice_array_to_slice((size_t)3U, prf_inputs, uint8_t[33U]),
      Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_slice randomness = Eurydice_array_to_subslice3(
        prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
        uint8_t *);
    int16_t sample_buffer[256U] = {0U};
    libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(randomness,
                                                                 sample_buffer);
    libcrux_ml_kem_polynomial_from_i16_array_d6_df(
        Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
        &Eurydice_slice_index(
            re_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
    libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_df(
        &Eurydice_slice_index(
            re_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
        scratch);
  }
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_77
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_77_fc(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_40(uint8_t *prf_input,
                                                  uint8_t domain_separator,
                                                  Eurydice_slice error_1,
                                                  int16_t *sample_buffer) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  Eurydice_slice uu____1 = core_array___Array_T__N___as_slice(
      (size_t)3U, prf_inputs, uint8_t[33U], Eurydice_slice);
  libcrux_ml_kem_hash_functions_portable_PRFxN_6e(
      uu____1, Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_slice randomness = Eurydice_array_to_subslice3(
        prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
        uint8_t *);
    libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(randomness,
                                                                 sample_buffer);
    libcrux_ml_kem_polynomial_from_i16_array_d6_df(
        Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
        &Eurydice_slice_index(
            error_1, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static inline void libcrux_ml_kem_hash_functions_portable_PRF_a6(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_6e
with const generics
- LEN= 128
*/
static inline void libcrux_ml_kem_hash_functions_portable_PRF_6e_a6(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_portable_PRF_a6(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_88
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_88_fc(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.entry
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d *
libcrux_ml_kem_matrix_entry_1b(Eurydice_slice matrix, size_t i, size_t j) {
  return &Eurydice_slice_index(
      matrix, i * (size_t)3U + j,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
        &myself->coefficients[j], (int16_t)1441);
    libcrux_ml_kem_vector_portable_add_b8(&myself->coefficients[j],
                                          &error->coefficients[j]);
    libcrux_ml_kem_vector_portable_barrett_reduce_b8(&myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  libcrux_ml_kem_polynomial_add_error_reduce_df(self, error);
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
    Eurydice_slice a_as_ntt, Eurydice_slice r_as_ntt, Eurydice_slice error_1,
    Eurydice_slice result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 =
          libcrux_ml_kem_matrix_entry_1b(a_as_ntt, i1, j);
      libcrux_ml_kem_polynomial_ntt_multiply_d6_df(
          uu____0,
          &Eurydice_slice_index(
              r_as_ntt, j, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
              libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
          scratch);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_1b(
          &Eurydice_slice_index(
              result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
              libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
          scratch);
    }
    libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(
        &Eurydice_slice_index(
            result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
        scratch);
    libcrux_ml_kem_polynomial_add_error_reduce_d6_df(
        &Eurydice_slice_index(
            result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
        &Eurydice_slice_index(
            error_1, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_compress_compress_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10,
            libcrux_secrets_int_as_u16_f5(a->elements[i0])));
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 10
*/
static inline void libcrux_ml_kem_vector_portable_compress_b8_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_ml_kem_vector_portable_compress_compress_ef(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_10_ff(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    Eurydice_slice serialized,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_df(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_portable_compress_b8_ef(scratch);
    libcrux_ml_kem_vector_portable_serialize_10_b8(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)20U * i0,
                                 (size_t)20U * i0 + (size_t)20U, uint8_t *));
  }
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    Eurydice_slice serialized,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_serialize_compress_then_serialize_10_ff(re, serialized,
                                                         scratch);
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
    Eurydice_slice out,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = input[i0];
    libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_fe(
        &re,
        Eurydice_slice_subslice3(
            out, i0 * ((size_t)960U / (size_t)3U),
            (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_c1_fc(
    Eurydice_slice randomness,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *matrix,
    Eurydice_slice ciphertext, Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  uint8_t domain_separator0 =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_40(
          r_as_ntt, prf_input, 0U, scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_1[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    error_1[i] = libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_77_fc(&lvalue, i);
  }
  int16_t sampling_buffer[256U] = {0U};
  uint8_t domain_separator = libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_40(
      prf_input, domain_separator0,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      sampling_buffer);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U] = {0U};
  libcrux_ml_kem_hash_functions_portable_PRF_6e_a6(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_sampling_sample_from_binomial_distribution_a0(
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t),
      sampling_buffer);
  libcrux_ml_kem_polynomial_from_i16_array_d6_df(
      Eurydice_array_to_slice((size_t)256U, sampling_buffer, int16_t), error_2);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    u[i] = libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_88_fc(&lvalue, i);
  }
  libcrux_ml_kem_matrix_compute_vector_u_1b(
      Eurydice_array_to_slice(
          (size_t)9U, matrix,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      r_as_ntt,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      Eurydice_array_to_slice(
          (size_t)3U, u, libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      scratch);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d copy_of_u[3U];
  memcpy(
      copy_of_u, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_compress_then_serialize_u_43(copy_of_u, ciphertext,
                                                      scratch->coefficients);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_vector_traits_decompress_1_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec) {
  libcrux_ml_kem_vector_portable_negate_b8(vec);
  libcrux_ml_kem_vector_portable_bitwise_and_with_constant_b8(vec,
                                                              (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_message_df(
    uint8_t *serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_deserialize_1_b8(
        Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                    (size_t)2U * i0 + (size_t)2U, uint8_t *),
        &re->coefficients[i0]);
    libcrux_ml_kem_vector_traits_decompress_1_df(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_message_error_reduce_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *result,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
        &result->coefficients[i0], (int16_t)1441);
    scratch[0U] = myself->coefficients[i0];
    libcrux_ml_kem_vector_portable_add_b8(scratch, &message->coefficients[i0]);
    libcrux_ml_kem_vector_portable_add_b8(&result->coefficients[i0], scratch);
    libcrux_ml_kem_vector_portable_barrett_reduce_b8(&result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_message_error_reduce_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *result,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_polynomial_add_message_error_reduce_df(self, message, result,
                                                        scratch);
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
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_ring_element_v_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_ntt_multiply_d6_df(
        &t_as_ntt[i0],
        &Eurydice_slice_index(
            r_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_1d,
            libcrux_ml_kem_polynomial_PolynomialRingElement_1d *),
        scratch);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_1b(result, scratch);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_1b(result, scratch);
  libcrux_ml_kem_polynomial_add_message_error_reduce_d6_df(
      error_2, message, result, scratch->coefficients);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_compress_compress_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4,
            libcrux_secrets_int_as_u16_f5(a->elements[i0])));
    a->elements[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 4
*/
static inline void libcrux_ml_kem_vector_portable_compress_b8_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a) {
  libcrux_ml_kem_vector_portable_compress_compress_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_4_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re,
    Eurydice_slice serialized,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_df(&re.coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_portable_compress_b8_d1(scratch);
    libcrux_ml_kem_vector_portable_serialize_4_b8(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *));
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, Eurydice_slice out,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_serialize_compress_then_serialize_4_df(re, out, scratch);
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
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    uint8_t *message, Eurydice_slice ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message_as_ring_element =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_serialize_deserialize_then_decompress_message_df(
      message, &message_as_ring_element);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_matrix_compute_ring_element_v_1b(
      t_as_ntt, r_as_ntt, error_2, &message_as_ring_element, &v, scratch);
  libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_6c(
      v, ciphertext, scratch->coefficients);
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
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_unpacked_28(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be *public_key,
    uint8_t *message, Eurydice_slice randomness, Eurydice_slice ciphertext,
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_ind_cpa_encrypt_c1_fc(
      randomness, public_key->A,
      Eurydice_slice_subslice3(ciphertext, (size_t)0U, (size_t)960U, uint8_t *),
      r_as_ntt, error_2, scratch);
  libcrux_ml_kem_ind_cpa_encrypt_c2_6c(
      public_key->t_as_ntt, r_as_ntt, error_2, message,
      Eurydice_slice_subslice_from(ciphertext, (size_t)960U, uint8_t, size_t,
                                   uint8_t[]),
      scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_28(
    Eurydice_slice public_key, uint8_t *message, Eurydice_slice randomness,
    Eurydice_slice ciphertext, Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be
      unpacked_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_50_89();
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_e2(public_key,
                                                          &unpacked_public_key);
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_28(&unpacked_public_key, message,
                                             randomness, ciphertext, r_as_ntt,
                                             error_2, scratch);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_kdf_39_1f(
    Eurydice_slice shared_secret, uint8_t *_, Eurydice_slice out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_decapsulate_d7(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_decrypt_42(
      ind_cpa_secret_key, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_portable_G_6e(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
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
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  libcrux_ml_kem_hash_functions_portable_PRF_6e_9e(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t));
  uint8_t expected_ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] = libcrux_ml_kem_ind_cca_decapsulate_call_mut_5f_d7(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_encrypt_28(
      ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      &error_2, &scratch);
  uint8_t implicit_rejection_shared_secret_kdf[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_1f(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t));
  uint8_t shared_secret_kdf[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_1f(
      shared_secret0, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t));
  uint8_t shared_secret[32U] = {0U};
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t));
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static inline void
libcrux_ml_kem_ind_cca_instantiations_portable_decapsulate_54(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_d7(private_key, ciphertext, ret);
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
  libcrux_ml_kem_ind_cca_instantiations_portable_decapsulate_54(
      private_key, ciphertext, ret);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_entropy_preprocess_39_f0(
    Eurydice_slice randomness, Eurydice_slice out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate.call_mut_c0
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_encapsulate_call_mut_c0_d9(void **_,
                                                  size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_encapsulate_d9(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  uint8_t processed_randomness[32U] = {0U};
  libcrux_ml_kem_variant_entropy_preprocess_39_f0(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t));
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t);
  libcrux_ml_kem_hash_functions_portable_H_6e(
      uu____0, Eurydice_array_to_subslice_from(
                   (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                   uint8_t, size_t, uint8_t[]));
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_portable_G_6e(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext =
      libcrux_ml_kem_types_default_73_80();
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] = libcrux_ml_kem_ind_cca_encapsulate_call_mut_c0_d9(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_encrypt_28(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_e6_d0(public_key),
                              uint8_t),
      processed_randomness, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, ciphertext.value, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      &error_2, &scratch);
  uint8_t shared_secret_array[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_1f(
      shared_secret, ciphertext.value,
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 = ciphertext;
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
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_portable_encapsulate_35(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_d9(public_key, randomness);
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
  return libcrux_ml_kem_ind_cca_instantiations_portable_encapsulate_35(
      public_key, randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,␣K>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,␣K>[TraitClause@0,␣TraitClause@1]}::default::closure<Vector,␣K>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1____default__closure_Vector__K__TraitClause_0__TraitClause_1___call_mut_1b(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
libcrux_ml_kem_ind_cpa_unpacked_default_70_1b(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1____default__closure_Vector__K__TraitClause_0__TraitClause_1___call_mut_1b(
            &lvalue, i);
  }
  memcpy(
      lit.secret_as_ntt, ret,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void libcrux_ml_kem_variant_cpa_keygen_seed_39_f0(
    Eurydice_slice key_generation_seed, Eurydice_slice out) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  libcrux_ml_kem_hash_functions_portable_G_6e(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_ae with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_call_mut_ae_b8(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_to_standard_domain_df(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vector) {
  libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
      vector,
      LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_polynomial_to_standard_domain_df(&myself->coefficients[j]);
    libcrux_ml_kem_vector_portable_add_b8(&myself->coefficients[j],
                                          &error->coefficients[j]);
    libcrux_ml_kem_vector_portable_barrett_reduce_b8(&myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  libcrux_ml_kem_polynomial_add_standard_error_reduce_df(self, error);
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
    Eurydice_slice matrix_A,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        libcrux_ml_kem_polynomial_ZERO_d6_df();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U; i1 < (size_t)3U; i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____1 =
          libcrux_ml_kem_matrix_entry_1b(matrix_A, i0, j);
      libcrux_ml_kem_polynomial_ntt_multiply_d6_df(uu____1, &s_as_ntt[j],
                                                   scratch);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_1b(&t_as_ntt[i0],
                                                          scratch);
    }
    libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_df(
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
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_b8(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be *public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_variant_cpa_keygen_seed_39_f0(
      key_generation_seed,
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, public_key->A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_57(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_40(
          Eurydice_array_to_slice(
              (size_t)3U, private_key->secret_as_ntt,
              libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
          prf_input, 0U, scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    error_as_ntt[i] =
        libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_call_mut_ae_b8(&lvalue,
                                                                        i);
  }
  libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_40(
      Eurydice_array_to_slice(
          (size_t)3U, error_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      prf_input, domain_separator, scratch->coefficients);
  libcrux_ml_kem_matrix_compute_As_plus_e_1b(
      public_key->t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)9U, public_key->A,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      private_key->secret_as_ntt, error_as_ntt, scratch);
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
libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_df(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_portable_serialize_12_b8(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)24U * i0,
                                 (size_t)24U * i0 + (size_t)24U, uint8_t *));
  }
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
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *key, Eurydice_slice out,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = key[i0];
    libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_df(
        &re, scratch,
        Eurydice_slice_subslice3(
            out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *));
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
    Eurydice_slice seed_for_a, Eurydice_slice serialized,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_ind_cpa_serialize_vector_1b(
      t_as_ntt,
      Eurydice_slice_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t *),
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from(
          serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static inline void libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_43(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    Eurydice_slice serialized_private_key, Eurydice_slice serialized_public_key,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *scratch) {
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      serialized_public_key, scratch);
  libcrux_ml_kem_ind_cpa_serialize_vector_1b(private_key->secret_as_ntt,
                                             serialized_private_key, scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_generate_keypair_90(
    Eurydice_slice key_generation_seed,
    Eurydice_slice serialized_ind_cpa_private_key,
    Eurydice_slice serialized_public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 private_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_70_1b();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be public_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_50_89();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_b8(
      key_generation_seed, &private_key, &public_key, scratch);
  libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_43(
      &public_key, &private_key, serialized_ind_cpa_private_key,
      serialized_public_key, scratch->coefficients);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_1f(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_ml_kem_hash_functions_portable_H_6e(
      public_key,
      Eurydice_array_to_subslice3(
          serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
          uint8_t *));
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____6 = serialized;
  size_t uu____7 = pointer;
  size_t uu____8 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____6, uu____7,
          uu____8 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
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
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_e6(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t ind_cpa_private_key[1152U] = {0U};
  uint8_t public_key[1184U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_generate_keypair_90(
      ind_cpa_keypair_randomness,
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t), &scratch);
  uint8_t secret_key_serialized[2400U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_1f(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 private_key =
      libcrux_ml_kem_types_from_77_28(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_d9 uu____1 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_74(
      uu____1, libcrux_ml_kem_types_from_fd_d0(copy_of_public_key));
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_portable_generate_keypair_06(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_e6(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_portable_generate_key_pair(uint8_t randomness[64U]) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_generate_keypair_06(
      randomness);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_only_1f(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U] = {0U};
  libcrux_ml_kem_hash_functions_portable_H_6e(
      Eurydice_array_to_subslice3(private_key->value, (size_t)384U * (size_t)3U,
                                  (size_t)768U * (size_t)3U + (size_t)32U,
                                  uint8_t *),
      Eurydice_array_to_slice((size_t)32U, t, uint8_t));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_5d(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_1f(private_key);
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
  return libcrux_ml_kem_ind_cca_validate_private_key_5d(private_key,
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
  return libcrux_ml_kem_ind_cca_validate_private_key_only_1f(private_key);
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
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key.call_mut_00
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_validate_public_key_call_mut_00_89(void **_,
                                                          size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
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
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    deserialized_pk[i] =
        libcrux_ml_kem_ind_cca_validate_public_key_call_mut_00_89(&lvalue, i);
  }
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key,
      libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, deserialized_pk,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  uint8_t public_key_serialized[1184U] = {0U};
  libcrux_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_ml_kem_vector_portable_ZERO_b8();
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____1 = deserialized_pk;
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1184U, public_key,
      libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      uu____1, uu____2,
      Eurydice_array_to_slice((size_t)1184U, public_key_serialized, uint8_t),
      &scratch);
  return Eurydice_array_eq((size_t)1184U, public_key, public_key_serialized,
                           uint8_t);
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
- $9size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be;

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
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
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be public_key;
} libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for
libcrux_ml_kem::ind_cca::unpacked::decapsulate::closure<Vector, Hasher, K,
K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE, PUBLIC_KEY_SIZE,
CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.decapsulate.call_mut_03 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_unpacked_decapsulate_call_mut_03_e7(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_decapsulate_e7(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_42(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_portable_G_6e(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
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
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  libcrux_ml_kem_hash_functions_portable_PRF_6e_9e(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t));
  uint8_t expected_ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] =
        libcrux_ml_kem_ind_cca_unpacked_decapsulate_call_mut_03_e7(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_28(
      &key_pair->public_key.ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      &error_2, &scratch);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t));
  uint8_t shared_secret_array[32U] = {0U};
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector,
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  memcpy(ret, shared_secret_array, (size_t)32U * sizeof(uint8_t));
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.decapsulate with const
generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_decapsulate_54(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_e7(key_pair, ciphertext, ret);
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
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_decapsulate_54(
      private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static inline void libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_f0(
    Eurydice_slice randomness, Eurydice_slice pk_hash, uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  uint8_t output[64U] = {0U};
  libcrux_ml_kem_hash_functions_portable_G_6e(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, output, uint8_t));
  memcpy(ret, output, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for
libcrux_ml_kem::ind_cca::unpacked::encapsulate::closure<Vector, Hasher, K,
K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE,
C2_SIZE, VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR,
VECTOR_U_BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.encapsulate.call_mut_f7 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_unpacked_encapsulate_call_mut_f7_e2(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_unpacked_encapsulate_e2(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_f0(
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
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] =
        libcrux_ml_kem_ind_cca_unpacked_encapsulate_call_mut_f7_e2(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_28(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      &error_2, &scratch);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 =
      libcrux_ml_kem_types_from_e0_80(copy_of_ciphertext);
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
- K_SQUARED= 9
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
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE tuple_c2
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_encapsulate_35(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *public_key,
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_e2(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
static inline tuple_c2 libcrux_ml_kem_mlkem768_portable_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *public_key,
    uint8_t randomness[32U]) {
  return libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_encapsulate_35(
      public_key, randomness);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_5a with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_ind_cca_unpacked_transpose_a_call_mut_5a_89(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_df();
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d
libcrux_ml_kem_polynomial_clone_c1_df(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector ret[16U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
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
- K_SQUARED= 9
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_transpose_a_89(
    Eurydice_slice ind_cpa_a,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[9U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    A[i] =
        libcrux_ml_kem_ind_cca_unpacked_transpose_a_call_mut_5a_89(&lvalue, i);
  }
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          libcrux_ml_kem_polynomial_clone_c1_df(
              libcrux_ml_kem_matrix_entry_1b(ind_cpa_a, j, i1));
      A[i1 * (size_t)3U + j] = uu____0;
    }
  }
  memcpy(
      ret, A,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_e6(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d scratch0 =
      libcrux_ml_kem_polynomial_ZERO_d6_df();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_b8(
      ind_cpa_keypair_randomness, &out->private_key.ind_cpa_private_key,
      &out->public_key.ind_cpa_public_key, &scratch0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[9U];
  libcrux_ml_kem_ind_cca_unpacked_transpose_a_89(
      Eurydice_array_to_slice(
          (size_t)9U, out->public_key.ind_cpa_public_key.A,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
      A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[9U];
  memcpy(
      uu____0, A,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(
      out->public_key.ind_cpa_public_key.A, uu____0,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  uint8_t pk_serialized[1184U] = {0U};
  libcrux_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_ml_kem_vector_portable_ZERO_b8();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t), &scratch);
  libcrux_ml_kem_hash_functions_portable_H_6e(
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t),
      Eurydice_array_to_slice((size_t)32U, out->public_key.public_key_hash,
                              uint8_t));
  uint8_t uu____1[32U];
  Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], TryFromSliceError);
  unwrap_26_b3(dst, uu____1);
  memcpy(out->private_key.implicit_rejection_value, uu____1,
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
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_generate_keypair_06(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_e6(copy_of_randomness, out);
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
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_generate_keypair_06(
      copy_of_randomness, key_pair);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_3f
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
libcrux_ml_kem_ind_cca_unpacked_default_3f_89(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be){
          .ind_cpa_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_50_89(),
          .public_key_hash = {0U}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_b1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
    libcrux_ml_kem_ind_cca_unpacked_default_b1_89(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____0 = {
      .ind_cpa_private_key = libcrux_ml_kem_ind_cpa_unpacked_default_70_1b(),
      .implicit_rejection_value = {0U}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_3f_89()});
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
static inline libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair(
    uint8_t randomness[64U]) {
  libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_b1_89();
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
  return libcrux_ml_kem_ind_cca_unpacked_default_b1_89();
}

/**
 Create a new, empty unpacked public key.
*/
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
libcrux_ml_kem_mlkem768_portable_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_3f_89();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_df(
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
      Eurydice_array_to_slice(
          (size_t)3U, key_pair->private_key.ind_cpa_private_key.secret_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_e2(
      ind_cpa_public_key, &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1152U, uint8_t,
                                   size_t, uint8_t[]),
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
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_keypair_from_private_key_ce(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_df(private_key,
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
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_keypair_from_private_key_ce(
      private_key, key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_b1 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_42(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  uint8_t ind_cpa_private_key[1152U] = {0U};
  uint8_t ind_cpa_public_key[1184U] = {0U};
  libcrux_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_ml_kem_vector_portable_ZERO_b8();
  libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_43(
      &self->public_key.ind_cpa_public_key,
      &self->private_key.ind_cpa_private_key,
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      &scratch);
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_1f(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_b1 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_b1_42(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk =
      libcrux_ml_kem_types_default_d3_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_42(self, &sk);
  return sk;
}

/**
 Get the serialized private key.
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_b1_42(key_pair);
}

/**
 Get the serialized private key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_42(key_pair,
                                                                   serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_6a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_6a_6c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *self) {
  uint8_t public_key[1184U] = {0U};
  libcrux_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_ml_kem_vector_portable_ZERO_b8();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t), &scratch);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_fd_d0(copy_of_public_key);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_b1 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_b1_6c(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_6a_6c(&self->public_key);
}

/**
 Get the serialized public key.
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_b1_6c(key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_6a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_6c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector scratch =
      libcrux_ml_kem_vector_portable_ZERO_b8();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      Eurydice_array_to_slice((size_t)1184U, serialized->value, uint8_t),
      &scratch);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_b1 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_b1_6c(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_6c(&self->public_key,
                                                       serialized);
}

/**
 Get the serialized public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_b1_6c(key_pair,
                                                                  serialized);
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_1c
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be
libcrux_ml_kem_ind_cpa_unpacked_clone_1c_89(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)3U, self->t_as_ntt, uu____0,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d, void *);
  uint8_t uu____1[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->seed_for_A, uu____1, uint8_t, void *);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_be lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[9U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)9U, self->A, ret,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d, void *);
  memcpy(
      lit.A, ret,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_86
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
libcrux_ml_kem_ind_cca_unpacked_clone_86_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *self) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be lit;
  lit.ind_cpa_public_key =
      libcrux_ml_kem_ind_cpa_unpacked_clone_1c_89(&self->ind_cpa_public_key);
  uint8_t ret[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->public_key_hash, ret, uint8_t, void *);
  memcpy(lit.public_key_hash, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_b1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *
libcrux_ml_kem_ind_cca_unpacked_public_key_b1_89(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
 Get the unpacked public key.
*/
static inline void libcrux_ml_kem_mlkem768_portable_unpacked_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *pk) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be uu____0 =
      libcrux_ml_kem_ind_cca_unpacked_clone_86_89(
          libcrux_ml_kem_ind_cca_unpacked_public_key_b1_89(key_pair));
  pk[0U] = uu____0;
}

/**
 Get the serialized public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be *public_key,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_6c(public_key, serialized);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash,
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_1e(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
        *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice_to((size_t)1184U, public_key->value,
                                    (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_1b(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, unpacked_public_key->ind_cpa_public_key.t_as_ntt,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)9U, unpacked_public_key->ind_cpa_public_key.A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      ret);
  libcrux_ml_kem_matrix_sample_matrix_A_57(uu____2, ret, false);
  libcrux_ml_kem_hash_functions_portable_H_6e(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_e6_d0(public_key),
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, unpacked_public_key->public_key_hash,
                              uint8_t));
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.unpack_public_key with
const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_unpack_public_key_a5(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_1e(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
static inline void
libcrux_ml_kem_mlkem768_portable_unpacked_unpacked_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_be
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_portable_unpacked_unpack_public_key_a5(
      public_key, unpacked_public_key);
}

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem768_portable_H_DEFINED
#endif /* libcrux_mlkem768_portable_H */
