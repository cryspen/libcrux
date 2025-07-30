/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 5807deab3f588567f00046b8ee83e4eba7cff5f6
 * Eurydice: 924e44f2e6e8caac37cddca618ba9488f0990ccc
 * Karamel: c56e0932f05c89c8c68089d909ad9c195f44a02c
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: 85ef3af5e4511668b215821a564d6537be61d44c
 */


#ifndef __libcrux_mlkem1024_avx2_H
#define __libcrux_mlkem1024_avx2_H

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
void
libcrux_ml_kem_mlkem1024_avx2_decapsulate(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext,
  uint8_t ret[32U]
);

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_fa
libcrux_ml_kem_mlkem1024_avx2_encapsulate(
  libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
  uint8_t randomness[32U]
);

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_avx2_generate_key_pair(uint8_t randomness[64U]);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_avx2_validate_private_key(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext
);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_avx2_validate_private_key_only(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key
);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_avx2_validate_public_key(
  libcrux_ml_kem_types_MlKemPublicKey_64 *public_key
);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem1024_avx2_H_DEFINED
#endif
