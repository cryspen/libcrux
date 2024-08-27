/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: 04413e808445c4f78fe89cd15b85ff549ed3be62
 * Libcrux: a6e4d55c8fe834886fcbfcdc09dbc3db0122f563
 */

#ifndef __libcrux_mlkem512_neon_H
#define __libcrux_mlkem512_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_neon.h"

void libcrux_ml_kem_mlkem512_neon_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

void libcrux_ml_kem_mlkem512_neon_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]);

tuple_ec libcrux_ml_kem_mlkem512_neon_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]);

tuple_ec libcrux_ml_kem_mlkem512_neon_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *public_key,
    uint8_t randomness[32U]);

libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_neon_generate_key_pair(uint8_t randomness[64U]);

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66
libcrux_ml_kem_mlkem512_neon_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

core_option_Option_04 libcrux_ml_kem_mlkem512_neon_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem512_neon_H_DEFINED
#endif
