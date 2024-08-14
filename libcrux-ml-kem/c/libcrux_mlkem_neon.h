/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 8de6020c10a3520a56fbf849176f8218e62435cf
 * Eurydice: f8fc97aeb6ecbaaacfe4baffcdc4d671989b5586
 * Karamel: 98e5d604741a886e20a526f6673077a15e23cead
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 0c66762ad2fdfb3f110ee362fa210bea0fecd265
 */

#ifndef __libcrux_mlkem_neon_H
#define __libcrux_mlkem_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3_neon.h"

void libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input,
                                          uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input,
                                          uint8_t ret[32U]);

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_neon_H_DEFINED
#endif
