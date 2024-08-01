/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: 1ed8ba551e8c65fdbad1bb7833bd7837be0d89b9
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 59864a878d97174338edf8868672aac0555a8814
 */

#ifndef __libcrux_mlkem1024_portable_H
#define __libcrux_mlkem1024_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"

void libcrux_ml_kem_mlkem1024_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

void libcrux_ml_kem_mlkem1024_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
    uint8_t randomness[32U]);

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem1024_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *public_key,
    uint8_t randomness[32U]);

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(uint8_t randomness[64U]);

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
libcrux_ml_kem_mlkem1024_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]);

core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__
libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t public_key);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem1024_portable_H_DEFINED
#endif
