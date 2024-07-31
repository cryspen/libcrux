/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: d5759a8b96e9f104664a88a83043d5761fcc9732
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: 3c5d3c5f94d5a7630aa83a84d6f06452e6c18807
 */

#ifndef __libcrux_mlkem_avx2_H
#define __libcrux_mlkem_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3.h"

void libcrux_ml_kem_hash_functions_avx2_G(Eurydice_slice input,
                                          uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input,
                                          uint8_t ret[32U]);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_avx2_H_DEFINED
#endif
