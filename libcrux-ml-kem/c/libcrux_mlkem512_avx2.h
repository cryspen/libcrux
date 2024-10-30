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
