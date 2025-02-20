/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: db4e045d4597d06d854ce7a2c10e8dcfda6ecd25
 * Eurydice: 75eae2e2534a16f5ba5430e6ee5c69d8a46f3bea
 * Karamel: 3823e3d82fa0b271d799b61c59ffb4742ddc1e65
 * F*: 7cd06c5562fc47ec14cd35c38034d5558a5ff762
 * Libcrux: f739ef6e9db364d07a61165242c78b62c81b91ef
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
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key);

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
