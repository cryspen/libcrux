/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 8f3c82290a95695e4f6bbaebc8317bfbe03233be
 * Karamel: d43a65c629e989afd6b21fa4486feda78a190a47
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: a23ad09369f2361317bfd6fd43267bd8521048eb
 */

#ifndef __libcrux_mlkem1024_neon_H
#define __libcrux_mlkem1024_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_neon.h"

void libcrux_ml_kem_mlkem1024_neon_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

void libcrux_ml_kem_mlkem1024_neon_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

tuple_21 libcrux_ml_kem_mlkem1024_neon_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]);

tuple_21 libcrux_ml_kem_mlkem1024_neon_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_2c *public_key,
    uint8_t randomness[32U]);

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_neon_generate_key_pair(uint8_t randomness[64U]);

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c
libcrux_ml_kem_mlkem1024_neon_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

core_option_Option_99 libcrux_ml_kem_mlkem1024_neon_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_1f public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem1024_neon_H_DEFINED
#endif
