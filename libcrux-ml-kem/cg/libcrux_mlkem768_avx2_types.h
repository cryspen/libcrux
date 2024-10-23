/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45f5a34f336e35c6cc2253bc90cbdb8d812cefa9
 * Eurydice: 1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c
 * Karamel: 8c3612018c25889288da6857771be3ad03b75bcd
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 897008ee57eed9e4574222a5e96d306ce203ecee
 */

#ifndef __libcrux_mlkem768_avx2_types_H
#define __libcrux_mlkem768_avx2_types_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

typedef __m256i libcrux_ml_kem_vector_avx2_SIMD256Vector;

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_f6_s {
  __m256i coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_f6;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_63 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63;

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768PublicKeyUnpacked;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63;

typedef struct libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_63 public_key;
} libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_avx2_types_H_DEFINED
#endif
