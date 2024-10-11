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
 * Libcrux: 2e8f138dbcbfbfabf4bbd994c8587ec00d197102
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
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext, uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_fa libcrux_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
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
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem1024_portable_H_DEFINED
#endif
