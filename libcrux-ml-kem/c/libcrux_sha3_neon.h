/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45f5a34f336e35c6cc2253bc90cbdb8d812cefa9
 * Eurydice: 1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c
 * Karamel: 8c3612018c25889288da6857771be3ad03b75bcd
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 2e8f138dbcbfbfabf4bbd994c8587ec00d197102
 */

#ifndef __libcrux_sha3_neon_H
#define __libcrux_sha3_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_arm64.h"
#include "libcrux_sha3_internal.h"

/**
 A portable SHA3 224 implementation.
*/
void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data);

/**
 A portable SHA3 256 implementation.
*/
void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data);

/**
 A portable SHA3 384 implementation.
*/
void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data);

/**
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data);

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1);

typedef struct libcrux_sha3_neon_x2_incremental_KeccakState_s {
  libcrux_sha3_generic_keccak_KeccakState_17 state[2U];
} libcrux_sha3_neon_x2_incremental_KeccakState;

/**
 Initialise the `KeccakState2`.
*/
libcrux_sha3_neon_x2_incremental_KeccakState
libcrux_sha3_neon_x2_incremental_init(void);

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1);

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1);

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1);

/**
 Squeeze five blocks
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1);

/**
 Shake256 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void libcrux_sha3_neon_x2_incremental_shake256_absorb_final(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1);

/**
 Squeeze block
*/
void libcrux_sha3_neon_x2_incremental_shake256_squeeze_first_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1);

/**
 Squeeze next block
*/
void libcrux_sha3_neon_x2_incremental_shake256_squeeze_next_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_neon_H_DEFINED
#endif
