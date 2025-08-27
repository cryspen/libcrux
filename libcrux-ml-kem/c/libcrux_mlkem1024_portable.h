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

#ifndef libcrux_mlkem1024_portable_H
#define libcrux_mlkem1024_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem1024_portable_decapsulate(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_2b libcrux_ml_kem_mlkem1024_portable_encapsulate(
    Eurydice_arr_00 *public_key, Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key_only(
    Eurydice_arr_17 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    Eurydice_arr_00 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem1024_portable_H_DEFINED
#endif /* libcrux_mlkem1024_portable_H */
