/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: db4e045d4597d06d854ce7a2c10e8dcfda6ecd25
 * Eurydice: 75eae2e2534a16f5ba5430e6ee5c69d8a46f3bea
 * Karamel: 3823e3d82fa0b271d799b61c59ffb4742ddc1e65
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: 834b7f51701fa4e8695a784c138ed230f49f0c4e
 */

#ifndef __libcrux_mlkem512_avx2_H
#define __libcrux_mlkem512_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext, uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_41 libcrux_ml_kem_mlkem512_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key,
    uint8_t randomness[32U]);

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_mlkem512_avx2_generate_key_pair(uint8_t randomness[64U]);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem512_avx2_H_DEFINED
#endif
