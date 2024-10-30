/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 3063d19312f8ec3af5945f24ed3ebbb6b6cd9678
 * Libcrux: 020cd93ab7a1437ba4a4c626b1acbf9fa14525ad
 */

#ifndef __libcrux_mlkem1024_portable_H
#define __libcrux_mlkem1024_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
void libcrux_ml_kem_mlkem1024_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *ciphertext, uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_21 libcrux_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]);

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(uint8_t randomness[64U]);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1f *ciphertext);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem1024_portable_H_DEFINED
#endif
