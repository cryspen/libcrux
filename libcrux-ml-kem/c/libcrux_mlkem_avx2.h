/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: 7efec1624422fd5e94388ef06b9c76dfe7a48d46
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 650b216aeb5901ec6f1c44ff275acd924e54bdbd
 * Libcrux: 2010f03fc3ff9700169ae4a5934fec93a09a1fc0
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

__m256i libcrux_ml_kem_vector_avx2_vec_zero(void);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_ZERO_ea(void);

__m256i libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_from_i16_array_ea(Eurydice_slice array);

void libcrux_ml_kem_vector_avx2_vec_to_i16_array(__m256i v, int16_t ret[16U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_to_i16_array_ea(__m256i x, int16_t ret[16U]);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs, __m256i rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_add_ea(__m256i lhs, __m256i *rhs);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs, __m256i rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_sub_ea(__m256i lhs, __m256i *rhs);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    __m256i vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_ea(__m256i vec,
                                                           int16_t c);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_ea(__m256i v,
                                                                int16_t c);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(
    __m256i vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_ea(__m256i v);

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
__m256i libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_barrett_reduce_ea(__m256i v);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i vector, int16_t constant);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_ea(
    __m256i v, int16_t r);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    __m256i vec, __m256i constants);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_ea(__m256i a, int16_t zeta0,
                                                       int16_t zeta1,
                                                       int16_t zeta2,
                                                       int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(__m256i vector,
                                                        int16_t zeta0,
                                                        int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_ea(__m256i a, int16_t zeta0,
                                                       int16_t zeta1);

__m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    __m128i vec, __m128i constants);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(__m256i vector,
                                                        int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_ea(__m256i a, int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_ea(
    __m256i a, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(__m256i vector,
                                                            int16_t zeta0,
                                                            int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_ea(__m256i a,
                                                           int16_t zeta0,
                                                           int16_t zeta1);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_ea(__m256i a,
                                                           int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
    __m256i vec);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(__m256i lhs, __m256i rhs,
                                                    int16_t zeta0,
                                                    int16_t zeta1,
                                                    int16_t zeta2,
                                                    int16_t zeta3);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_multiply_ea(__m256i *lhs, __m256i *rhs,
                                                   int16_t zeta0, int16_t zeta1,
                                                   int16_t zeta2,
                                                   int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    __m256i vector);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_compress_1_ea(__m256i v);

__m256i libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(__m256i lhs,
                                                              __m256i rhs);

void libcrux_ml_kem_vector_avx2_serialize_serialize_1(__m256i vector,
                                                      uint8_t ret[2U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_1_ea(__m256i a, uint8_t ret[2U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_1(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_1_ea(Eurydice_slice a);

void libcrux_ml_kem_vector_avx2_serialize_serialize_4(__m256i vector,
                                                      uint8_t ret[8U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_4_ea(__m256i a, uint8_t ret[8U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_4(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_4_ea(Eurydice_slice a);

void libcrux_ml_kem_vector_avx2_serialize_serialize_5(__m256i vector,
                                                      uint8_t ret[10U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_5_ea(__m256i a, uint8_t ret[10U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_5(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_5_ea(Eurydice_slice a);

void libcrux_ml_kem_vector_avx2_serialize_serialize_10(__m256i vector,
                                                       uint8_t ret[20U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_10_ea(__m256i a, uint8_t ret[20U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_10(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_10_ea(Eurydice_slice a);

void libcrux_ml_kem_vector_avx2_serialize_serialize_11(__m256i vector,
                                                       uint8_t ret[22U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_11_ea(__m256i a, uint8_t ret[22U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_11(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_11_ea(Eurydice_slice a);

void libcrux_ml_kem_vector_avx2_serialize_serialize_12(__m256i vector,
                                                       uint8_t ret[24U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
void libcrux_ml_kem_vector_avx2_serialize_12_ea(__m256i a, uint8_t ret[24U]);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_12(
    Eurydice_slice bytes);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_12_ea(Eurydice_slice a);

size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector)}
*/
size_t libcrux_ml_kem_vector_avx2_rej_sample_ea(Eurydice_slice a,
                                                Eurydice_slice out);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(__m256i vector,
                                                            int16_t zeta);

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector)#1}
*/
__m256i libcrux_ml_kem_vector_avx2_clone_3a(__m256i *self);

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_d2_s {
  __m256i coefficients[16U];
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
