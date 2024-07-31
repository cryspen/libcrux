/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 8db8a4838ea46c9ac681ba1051d1d296dd0d54b7
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8
 * Libcrux: d992e8bff91dab77b6f0abebf16384ce422b310c
 */

#ifndef __libcrux_sha3_neon_H
#define __libcrux_sha3_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_arm64.h"
#include "libcrux_core.h"
#include "libcrux_sha3_internal.h"
#include "libcrux_sha3_libcrux_ml_kem.h"

void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1);

libcrux_sha3_generic_keccak_KeccakState__uint8_t__2size_t
libcrux_sha3_neon_x2_incremental_shake128_init(void);

void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState__uint8_t__2size_t *s,
    Eurydice_slice data0, Eurydice_slice data1);

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState__uint8_t__2size_t *s,
    Eurydice_slice out0, Eurydice_slice out1);

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState__uint8_t__2size_t *s,
    Eurydice_slice out0, Eurydice_slice out1);

void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_neon_H_DEFINED
#endif
