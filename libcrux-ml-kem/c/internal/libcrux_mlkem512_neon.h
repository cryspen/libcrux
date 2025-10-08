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

#ifndef internal_libcrux_mlkem512_neon_H
#define internal_libcrux_mlkem512_neon_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_mlkem512_neon.h"
#include "internal/libcrux_mlkem_neon.h"
#include "libcrux_core.h"

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512PublicKeyUnpacked;

/**
 Decapsulate ML-KEM 512 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem512KeyPairUnpacked`] and an [`MlKem512Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem512_neon_unpacked_decapsulate(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *private_key,
    Eurydice_arr_56 *ciphertext);

/**
 Encapsulate ML-KEM 512 (unpacked)

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem512PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_17 libcrux_ml_kem_mlkem512_neon_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *public_key,
    Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair);

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_neon_unpacked_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_neon_unpacked_init_key_pair(void);

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
libcrux_ml_kem_mlkem512_neon_unpacked_init_public_key(void);

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_key_pair_from_private_mut(
    Eurydice_arr_7f0 *private_key,
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair);

/**
 Get the serialized private key.
*/
Eurydice_arr_7f0
libcrux_ml_kem_mlkem512_neon_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair);

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_7f0 *serialized);

/**
 Get the serialized public key.
*/
Eurydice_arr_30
libcrux_ml_kem_mlkem512_neon_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair);

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_30 *serialized);

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *public_key,
    Eurydice_arr_30 *serialized);

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem512_neon_unpacked_unpacked_public_key(
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
        *unpacked_public_key);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_mlkem512_neon_H_DEFINED
#endif /* internal_libcrux_mlkem512_neon_H */
