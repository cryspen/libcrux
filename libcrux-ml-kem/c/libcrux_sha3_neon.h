/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: b2946d0484e60b53f4c3d553c8101d92661a28da
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: 5cb76a308d9917075a99825e1881852009a4a910
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
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data);

/**
 A portable SHA3 256 implementation.
*/
void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data);

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1);

typedef struct libcrux_sha3_neon_x2_incremental_KeccakState_s {
  libcrux_sha3_generic_keccak_KeccakState_48 state[2U];
} libcrux_sha3_neon_x2_incremental_KeccakState;

/**
 Initialise the `KeccakState2`.
*/
libcrux_sha3_neon_x2_incremental_KeccakState
libcrux_sha3_neon_x2_incremental_shake128_init(void);

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
 A portable SHA3 224 implementation.
*/
void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data);

/**
 A portable SHA3 384 implementation.
*/
void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_neon_H_DEFINED
#endif
