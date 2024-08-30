/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0576bfc67e99aae86c51930421072688138b672b
 * Eurydice: e66abbc2119485abfafa17c1911bdbdada5b04f3
 * Karamel: 7862fdc3899b718d39ec98568f78ec40592a622a
 * F*: 04413e808445c4f78fe89cd15b85ff549ed3be62
 * Libcrux: 37cab5179bba258e13e25e12d3d720f8bb922382
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
