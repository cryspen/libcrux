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

#ifndef __libcrux_mlkem768_avx2_H
#define __libcrux_mlkem768_avx2_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
void libcrux_ml_kem_mlkem768_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_c2 libcrux_ml_kem_mlkem768_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t randomness[32U]);

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_avx2_generate_key_pair(uint8_t randomness[64U]);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_avx2_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_avx2_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_avx2_H_DEFINED
#endif
