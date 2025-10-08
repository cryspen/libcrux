/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: c66a520f7072006af0071eb517002a73d5f3a7d1
 * Eurydice: 9dae7cbf24d38b7b0eb8e7efd12d662a4ebe1f1a
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: fba8ff3916a9aa0a3869f2fffea66d8aea07144a
 */

#ifndef libcrux_mlkem768_neon_H
#define libcrux_mlkem768_neon_H

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
Eurydice_arr_60 libcrux_ml_kem_mlkem768_neon_decapsulate(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext);

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_56 libcrux_ml_kem_mlkem768_neon_encapsulate(Eurydice_arr_74 *public_key,
                                                  Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_neon_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_private_key(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_private_key_only(
    Eurydice_arr_ea *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_public_key(
    Eurydice_arr_74 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem768_neon_H_DEFINED
#endif /* libcrux_mlkem768_neon_H */
