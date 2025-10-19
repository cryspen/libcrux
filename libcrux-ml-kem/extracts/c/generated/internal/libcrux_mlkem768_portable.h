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

#ifndef internal_libcrux_mlkem768_portable_H
#define internal_libcrux_mlkem768_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_mlkem768_portable.h"
#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"
#include "libcrux_sha3_internal.h"

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768PublicKeyUnpacked;

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem768_portable_unpacked_decapsulate(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *private_key,
    Eurydice_arr_2c *ciphertext);

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_56 libcrux_ml_kem_mlkem768_portable_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    Eurydice_arr_60 randomness);

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair);

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_portable_unpacked_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness);

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_portable_unpacked_init_key_pair(void);

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_mlkem768_portable_unpacked_init_public_key(void);

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_from_private_mut(
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair);

/**
 Get the serialized private key.
*/
Eurydice_arr_ea
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair);

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_ea *serialized);

/**
 Get the serialized public key.
*/
Eurydice_arr_74
libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair);

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_74 *serialized);

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_public_key(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *pk);

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    Eurydice_arr_74 *serialized);

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem768_portable_unpacked_unpacked_public_key(
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_mlkem768_portable_H_DEFINED
#endif /* internal_libcrux_mlkem768_portable_H */
