/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 2b71c3c42337fe17ceca860bedaafb3443e6c5e8
 * Eurydice: dcfae68c874635956f71d4c05928841b29ad0a8b
 * Karamel: 87384b244a98a0c41a2e14c65b872d885af7c8df
 * F*: 8b6fce63ca91b16386d8f76e82ea87a3c109a208
 * Libcrux: 4b0d78759e0adf160bab80862883bd5ba7338977
 */

#ifndef __libcrux_mlkem768_portable_types_H
#define __libcrux_mlkem768_portable_types_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_s {
  int16_t elements[16U];
} libcrux_ml_kem_vector_portable_vector_type_PortableVector;

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_1d_s {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_1d;

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
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0;

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

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_portable_types_H_DEFINED
#endif
