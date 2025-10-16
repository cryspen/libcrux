/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: ec7dfaf71369de6c7ab306a7ada725b6fc004a33
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 23ba8451a39d29970cc274e93bb0b2fe91fbc040
 */


#ifndef internal_libcrux_mlkem512_portable_H
#define internal_libcrux_mlkem512_portable_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"
#include "../libcrux_mlkem512_portable.h"

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512PublicKeyUnpacked;

/**
 Decapsulate ML-KEM 512 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type [`MlKem512KeyPairUnpacked`]
 and an [`MlKem512Ciphertext`].
*/
Eurydice_arr_60
libcrux_ml_kem_mlkem512_portable_unpacked_decapsulate(
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *private_key,
  Eurydice_arr_56 *ciphertext
);

/**
 Encapsulate ML-KEM 512 (unpacked)

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type [`MlKem512PublicKeyUnpacked`],
 the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_17
libcrux_ml_kem_mlkem512_portable_unpacked_encapsulate(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
  Eurydice_arr_60 randomness
);

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_generate_key_pair_mut(
  libcrux_sha3_Sha3_512Digest randomness,
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair
);

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_portable_unpacked_generate_key_pair(
  libcrux_sha3_Sha3_512Digest randomness
);

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_portable_unpacked_init_key_pair(void);

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
libcrux_ml_kem_mlkem512_portable_unpacked_init_public_key(void);

/**
 Get an unpacked key from a private key.
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_from_private_mut(
  Eurydice_arr_7f0 *private_key,
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair
);

/**
 Get the serialized private key.
*/
Eurydice_arr_7f0
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_private_key(
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair
);

/**
 Get the serialized private key.
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_private_key_mut(
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
  Eurydice_arr_7f0 *serialized
);

/**
 Get the serialized public key.
*/
Eurydice_arr_30
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_public_key(
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair
);

/**
 Get the serialized public key.
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_public_key_mut(
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
  Eurydice_arr_30 *serialized
);

/**
 Get the serialized public key.
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_serialized_public_key(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
  Eurydice_arr_30 *serialized
);

/**
 Get the unpacked public key.
*/
void
libcrux_ml_kem_mlkem512_portable_unpacked_unpacked_public_key(
  Eurydice_arr_30 *public_key,
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *unpacked_public_key
);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_mlkem512_portable_H_DEFINED
#endif /* internal_libcrux_mlkem512_portable_H */
