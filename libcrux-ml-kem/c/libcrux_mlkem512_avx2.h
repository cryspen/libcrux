/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 564ce891b07fd4aefe7d5ccd78e61400b4ac4a2b
 * Karamel: 06a6d2fb3a547d11c9f6dbec26f1f9b5e0dbf411
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#ifndef libcrux_mlkem512_avx2_H
#define libcrux_mlkem512_avx2_H

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
Eurydice_arr_60 libcrux_ml_kem_mlkem512_avx2_decapsulate(
    Eurydice_arr_7f *private_key, Eurydice_arr_56 *ciphertext);

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_17 libcrux_ml_kem_mlkem512_avx2_encapsulate(Eurydice_arr_30 *public_key,
                                                  Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_mlkem512_avx2_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_private_key(
    Eurydice_arr_7f *private_key, Eurydice_arr_56 *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_private_key_only(
    Eurydice_arr_7f *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_avx2_validate_public_key(
    Eurydice_arr_30 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem512_avx2_H_DEFINED
#endif /* libcrux_mlkem512_avx2_H */
