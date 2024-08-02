/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: be0d5b5e1455673c2afa9592c0951def463f59ec
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: cb6da975011a1d6dfeaa6215d63a56d043b522b5
 */

#ifndef __libcrux_mlkem512_portable_H
#define __libcrux_mlkem512_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"

void libcrux_ml_kem_mlkem512_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

void libcrux_ml_kem_mlkem512_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]);

tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *public_key,
    uint8_t randomness[32U]);

libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_portable_generate_key_pair(uint8_t randomness[64U]);

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae
libcrux_ml_kem_mlkem512_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

core_option_Option_04 libcrux_ml_kem_mlkem512_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem512_portable_H_DEFINED
#endif
