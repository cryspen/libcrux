/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: 3c77f1ac8116257d0c416fdac562edfa178b860b
 * Karamel: b2cba1e3f23fd7a54cf0b515f95089cfba8d39c3
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: e8559e89862ec3b3110d5c297735d28534aaef54
 */

#ifndef libcrux_mlkem512_portable_H
#define libcrux_mlkem512_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem512_portable_decapsulate(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext);

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_17 libcrux_ml_kem_mlkem512_portable_encapsulate(
    Eurydice_arr_30 *public_key, Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_mlkem512_portable_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key_only(
    Eurydice_arr_7f0 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_public_key(
    Eurydice_arr_30 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem512_portable_H_DEFINED
#endif /* libcrux_mlkem512_portable_H */
