/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: d6e4d1bb9c27c4eebbebcb29ba8bea1d58741421
 * Karamel: 2bd16e63cfbfa2b81d3c45d597b811ca2a12d430
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: a7de672380a622d67efb35e3707a528e375cbf76
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

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types libcrux_intrinsics_arm64_extract__uint64x2_t
with const generics
- $2size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_cc_s {
  _uint64x2_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_cc;

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

/**
 Initialise the `KeccakState2`.
*/
libcrux_sha3_generic_keccak_KeccakState_cc
libcrux_sha3_neon_x2_incremental_shake128_init(void);

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice data0,
    Eurydice_slice data1);

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out0,
    Eurydice_slice out1);

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_cc *s, Eurydice_slice out0,
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
