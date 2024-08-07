/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 75bf8bca5f9903b4f6e8fba693d61af1415d512f
 */

#ifndef __libcrux_mlkem_portable_H
#define __libcrux_mlkem_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3.h"
#include "libcrux_sha3_internal.h"

void libcrux_ml_kem_hash_functions_portable_G(Eurydice_slice input,
                                              uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_portable_H(Eurydice_slice input,
                                              uint8_t ret[32U]);

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS ((int16_t)3329)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS \
  ((int16_t)1353)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (62209U)

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_s {
  int16_t elements[16U];
} libcrux_ml_kem_vector_portable_vector_type_PortableVector;

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(Eurydice_slice array);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_from_i16_array_0d(Eurydice_slice array);

typedef struct uint8_t_x11_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
  uint8_t f5;
  uint8_t f6;
  uint8_t f7;
  uint8_t f8;
  uint8_t f9;
  uint8_t f10;
} uint8_t_x11;

uint8_t_x11 libcrux_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_slice v);

void libcrux_ml_kem_vector_portable_serialize_serialize_11(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[22U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_11_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[22U]);

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

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_slice bytes);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_zero(void);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_11(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_11_0d(Eurydice_slice a);

void libcrux_ml_kem_vector_portable_vector_type_to_i16_array(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    int16_t ret[16U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_to_i16_array_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    int16_t ret[16U]);

extern const uint8_t
    libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[256U]
                                                                         [16U];

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ZERO_0d(void);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_add(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_add_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_sub(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_sub_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_multiply_by_constant_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_bitwise_and_with_constant_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_cond_subtract_3329_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int32_t)20159)

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_SHIFT ((int32_t)26)

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_R \
  ((int32_t)1 << (uint32_t)                                 \
       LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_SHIFT)

int16_t libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_barrett_reduce_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (16U)

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_R \
  ((int32_t)1 << (uint32_t)                                    \
       LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT)

int16_t libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
    int32_t value);

int16_t libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t r);

uint8_t libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_compress_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_1_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v);

uint32_t libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value);

int16_t libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe);

void libcrux_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v, int16_t zeta,
    size_t i, size_t j);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_1_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta0,
    int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_2_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_3_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta);

void libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *v, int16_t zeta,
    size_t i, size_t j);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta0,
    int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta);

void libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *b, int16_t zeta,
    size_t i, size_t j,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *out);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_multiply_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

void libcrux_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[2U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_1_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[2U]);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_1(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_1_0d(Eurydice_slice a);

typedef struct uint8_t_x4_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
} uint8_t_x4;

uint8_t_x4 libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
    Eurydice_slice v);

void libcrux_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[8U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_4_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[8U]);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_4(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_4_0d(Eurydice_slice a);

typedef struct uint8_t_x5_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
} uint8_t_x5;

uint8_t_x5 libcrux_ml_kem_vector_portable_serialize_serialize_5_int(
    Eurydice_slice v);

void libcrux_ml_kem_vector_portable_serialize_serialize_5(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[10U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_5_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[10U]);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_slice bytes);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_5(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_5_0d(Eurydice_slice a);

uint8_t_x5 libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_slice v);

void libcrux_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[20U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_10_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[20U]);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_10(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_10_0d(Eurydice_slice a);

typedef struct uint8_t_x3_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
} uint8_t_x3;

uint8_t_x3 libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_slice v);

void libcrux_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[24U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_vector_portable_serialize_12_0d(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[24U]);

typedef struct int16_t_x2_s {
  int16_t fst;
  int16_t snd;
} int16_t_x2;

int16_t_x2 libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes);

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_12(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_12_0d(Eurydice_slice a);

size_t libcrux_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_slice a, Eurydice_slice result);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
size_t libcrux_ml_kem_vector_portable_rej_sample_0d(Eurydice_slice a,
                                                    Eurydice_slice out);

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_clone_3b(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *self);

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_f0_s {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_f0;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_42_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 secret_as_ntt[4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_42;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_42_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_42
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_42;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_42_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 A[4U][4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_42;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_42_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_42 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_42;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_42_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_42 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_42 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_42;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_ae_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 secret_as_ntt[2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_ae;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ae_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_ae
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ae;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ae_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 A[2U][2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ae;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ae ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ae private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_f8_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_f8;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_f8_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_f8
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_f8;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_f8_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f0 A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_f8;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_f8_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_f8 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_f8;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_f8_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_f8 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_f8 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_f8;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_portable_H_DEFINED
#endif
