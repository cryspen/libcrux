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

#ifndef __libcrux_mlkem_avx2_H
#define __libcrux_mlkem_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"
#include "libcrux_sha3.h"
#include "libcrux_sha3_avx2.h"

void libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input,
                                          uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input,
                                          uint8_t ret[32U]);

libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_zero(void);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_ZERO_ea(void);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice array);

void libcrux_ml_kem_vector_avx2_to_i16_array(
    libcrux_intrinsics_avx2_extract_Vec256 v, int16_t ret[16U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_to_i16_array_ea(
    libcrux_intrinsics_avx2_extract_Vec256 x, int16_t ret[16U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_add(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_add_ea(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 *rhs);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_sub(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_sub_ea(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 *rhs);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(
    libcrux_intrinsics_avx2_extract_Vec256 v, int16_t c);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t constant);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_barrett_reduce_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t constant);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_compress_1_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 rhs);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    libcrux_intrinsics_avx2_extract_Vec256 v,
    libcrux_intrinsics_avx2_extract_Vec256 c);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0,
    int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0,
    int16_t zeta1);

libcrux_intrinsics_avx2_extract_Vec128
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    libcrux_intrinsics_avx2_extract_Vec128 v,
    libcrux_intrinsics_avx2_extract_Vec128 c);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0,
    int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta0,
    int16_t zeta1);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, int16_t zeta);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
    libcrux_intrinsics_avx2_extract_Vec256 v);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(
    libcrux_intrinsics_avx2_extract_Vec256 lhs,
    libcrux_intrinsics_avx2_extract_Vec256 rhs, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_ntt_multiply_ea(
    libcrux_intrinsics_avx2_extract_Vec256 *lhs,
    libcrux_intrinsics_avx2_extract_Vec256 *rhs, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3);

void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[2U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_1_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[2U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_1(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_1_ea(Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[8U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_4_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[8U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_4(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_4_ea(Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[10U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_5_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[10U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_5(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_5_ea(Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[20U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_10_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[20U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_10(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_10_ea(Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[22U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_11_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[22U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_11(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_11_ea(Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[24U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_12_ea(
    libcrux_intrinsics_avx2_extract_Vec256 vector, uint8_t ret[24U]);

libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_serialize_deserialize_12(Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
libcrux_intrinsics_avx2_extract_Vec256
libcrux_ml_kem_vector_avx2_deserialize_12_ea(Eurydice_slice bytes);

size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
size_t libcrux_ml_kem_vector_avx2_rej_sample_ea(Eurydice_slice input,
                                                Eurydice_slice output);

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#1}
*/
libcrux_intrinsics_avx2_extract_Vec256 libcrux_ml_kem_vector_avx2_clone_3a(
    libcrux_intrinsics_avx2_extract_Vec256 *self);

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_d2_s {
  libcrux_intrinsics_avx2_extract_Vec256 coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_d2;

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
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_01_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_01
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_01;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[4U][4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_01 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_01 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 secret_as_ntt[2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d6_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d6
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d6;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_d2 A[2U][2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d6 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d6 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_avx2_H_DEFINED
#endif
