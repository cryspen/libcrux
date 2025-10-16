/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9b87e8727803cd306b94c18b0ceb0b5b1c18c0e9
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */


#ifndef libcrux_mlkem1024_neon_H
#define libcrux_mlkem1024_neon_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
*/
Eurydice_arr_60
libcrux_ml_kem_mlkem1024_neon_decapsulate(
  Eurydice_arr_17 *private_key,
  Eurydice_arr_00 *ciphertext
);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_2b
libcrux_ml_kem_mlkem1024_neon_encapsulate(
  Eurydice_arr_00 *public_key,
  Eurydice_arr_60 randomness
);

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_neon_generate_key_pair(libcrux_sha3_Sha3_512Digest randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_neon_validate_private_key(
  Eurydice_arr_17 *private_key,
  Eurydice_arr_00 *ciphertext
);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_neon_validate_private_key_only(Eurydice_arr_17 *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_neon_validate_public_key(Eurydice_arr_00 *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem1024_neon_H_DEFINED
#endif /* libcrux_mlkem1024_neon_H */
