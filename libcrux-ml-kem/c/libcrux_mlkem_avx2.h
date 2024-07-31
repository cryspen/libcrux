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
#include "libcrux_sha3_libcrux_ml_kem.h"

void libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input,
                                          uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input,
                                          uint8_t ret[32U]);

uint8_t libcrux_ml_kem_vector_avx2_zero(void);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ZERO(
    void);

uint8_t libcrux_ml_kem_vector_avx2_from_i16_array(Eurydice_slice array);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___from_i16_array(
    Eurydice_slice array);

void libcrux_ml_kem_vector_avx2_to_i16_array(uint8_t v, int16_t ret[16U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___to_i16_array(
    uint8_t x, int16_t ret[16U]);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_add(uint8_t lhs, uint8_t rhs);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___add(
    uint8_t lhs, uint8_t *rhs);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_sub(uint8_t lhs, uint8_t rhs);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___sub(
    uint8_t lhs, uint8_t *rhs);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    uint8_t vector, int16_t constant);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___multiply_by_constant(
    uint8_t v, int16_t c);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    uint8_t vector, int16_t constant);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___bitwise_and_with_constant(
    uint8_t vector, int16_t constant);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(
    uint8_t vector);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___cond_subtract_3329(
    uint8_t vector);

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(uint8_t vector);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___barrett_reduce(
    uint8_t vector);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    uint8_t vector, int16_t constant);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___montgomery_multiply_by_constant(
    uint8_t vector, int16_t constant);

uint8_t libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    uint8_t vector);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___compress_1(
    uint8_t vector);

uint8_t libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(uint8_t lhs,
                                                              uint8_t rhs);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    uint8_t v, uint8_t c);

uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(uint8_t vector,
                                                        int16_t zeta0,
                                                        int16_t zeta1);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1);

uint8_t
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    uint8_t v, uint8_t c);

uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(uint8_t vector,
                                                        int16_t zeta);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_layer_3_step(
    uint8_t vector, int16_t zeta);

uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_1_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(uint8_t vector,
                                                            int16_t zeta0,
                                                            int16_t zeta1);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_2_step(
    uint8_t vector, int16_t zeta0, int16_t zeta1);

uint8_t libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(uint8_t vector,
                                                            int16_t zeta);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___inv_ntt_layer_3_step(
    uint8_t vector, int16_t zeta);

uint8_t libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(uint8_t v);

uint8_t libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(uint8_t lhs, uint8_t rhs,
                                                    int16_t zeta0,
                                                    int16_t zeta1,
                                                    int16_t zeta2,
                                                    int16_t zeta3);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___ntt_multiply(
    uint8_t *lhs, uint8_t *rhs, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

void libcrux_ml_kem_vector_avx2_serialize_serialize_1(uint8_t vector,
                                                      uint8_t ret[2U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_1(
    uint8_t vector, uint8_t ret[2U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_1(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_1(
    Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_4(uint8_t vector,
                                                      uint8_t ret[8U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_4(
    uint8_t vector, uint8_t ret[8U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_4(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_4(
    Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_5(uint8_t vector,
                                                      uint8_t ret[10U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_5(
    uint8_t vector, uint8_t ret[10U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_5(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_5(
    Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_10(uint8_t vector,
                                                       uint8_t ret[20U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_10(
    uint8_t vector, uint8_t ret[20U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_10(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_10(
    Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_11(uint8_t vector,
                                                       uint8_t ret[22U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_11(
    uint8_t vector, uint8_t ret[22U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_11(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_11(
    Eurydice_slice bytes);

void libcrux_ml_kem_vector_avx2_serialize_serialize_12(uint8_t vector,
                                                       uint8_t ret[24U]);

void libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___serialize_12(
    uint8_t vector, uint8_t ret[24U]);

uint8_t libcrux_ml_kem_vector_avx2_serialize_deserialize_12(
    Eurydice_slice bytes);

uint8_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___deserialize_12(
    Eurydice_slice bytes);

size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output);

size_t
libcrux_ml_kem_vector_avx2___libcrux_ml_kem__vector__traits__Operations_for_libcrux_ml_kem__vector__avx2__SIMD256Vector___rej_sample(
    Eurydice_slice input, Eurydice_slice output);

uint8_t
libcrux_ml_kem_vector_avx2___core__clone__Clone_for_libcrux_ml_kem__vector__avx2__SIMD256Vector__1__clone(
    uint8_t *self);

typedef struct
    libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector_s {
  uint8_t coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t
      public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__3size_t;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[4U][4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t
      public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__4size_t;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      secret_as_ntt[2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t;

typedef struct
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement__libcrux_ml_kem_vector_avx2_SIMD256Vector
      A[2U][2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t;

typedef struct
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_avx2_H_DEFINED
#endif
