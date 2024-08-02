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

#ifndef __libcrux_mlkem768_neon_H
#define __libcrux_mlkem768_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_neon.h"

void libcrux_ml_kem_mlkem768_neon_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

void libcrux_ml_kem_mlkem768_neon_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

tuple_3c libcrux_ml_kem_mlkem768_neon_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]);

tuple_3c libcrux_ml_kem_mlkem768_neon_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_fd *public_key,
    uint8_t randomness[32U]);

libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_neon_generate_key_pair(uint8_t randomness[64U]);

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd
libcrux_ml_kem_mlkem768_neon_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

core_option_Option_92 libcrux_ml_kem_mlkem768_neon_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_15 public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem768_neon_H_DEFINED
#endif
