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

#ifndef __libcrux_sha3_avx2_H
#define __libcrux_sha3_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_sha3_neon.h"

void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3);

typedef struct libcrux_sha3_avx2_x4_incremental_KeccakState_s {
  libcrux_sha3_generic_keccak_KeccakState_fc state[2U];
} libcrux_sha3_avx2_x4_incremental_KeccakState;

libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_sha3_avx2_x4_incremental_init(void);

void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3);

void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3);

void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
