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
 * Libcrux: f36c80b7aa99ddcaefe9c46f4705e4ad30c0870a
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
