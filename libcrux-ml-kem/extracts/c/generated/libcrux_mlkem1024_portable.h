/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 0b834617366280f902ccc302d8920f2d508fba45
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 3820cfd1cfca2935e0c8da6a75c5a64ba0911e58
 */

#ifndef libcrux_mlkem1024_portable_H
#define libcrux_mlkem1024_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"
#include "libcrux_sha3_internal.h"

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
