/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: f4283998bcc3c86677cf0e03a6fa71913a524658
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: 878f09c21a4312320518388a0d902986b08e030a
 */

#ifndef __libcrux_mlkem512_avx2_H
#define __libcrux_mlkem512_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_avx2.h"

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

/**
 Decapsulate ML-KEM 512 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem512KeyPairUnpacked`] and an [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_avx2_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_ec libcrux_ml_kem_mlkem512_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]);

/**
 Encapsulate ML-KEM 512 (unpacked)

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem512PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_ec libcrux_ml_kem_mlkem512_avx2_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d6 *public_key,
    uint8_t randomness[32U]);

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_avx2_generate_key_pair(uint8_t randomness[64U]);

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_d6
libcrux_ml_kem_mlkem512_avx2_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

/**
 Validate a public key.

 Returns `Some(public_key)` if valid, and `None` otherwise.
*/
core_option_Option_04 libcrux_ml_kem_mlkem512_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem512_avx2_H_DEFINED
#endif
