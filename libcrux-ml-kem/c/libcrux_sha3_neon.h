/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: 23480eeb26f8e66cfa9bd0eb76c65d87fbb91806
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- $2size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_fc_s {
  core_core_arch_arm_shared_neon_uint64x2_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_fc;

void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice out0, Eurydice_slice out1);

libcrux_sha3_generic_keccak_KeccakState_fc
libcrux_sha3_neon_x2_incremental_shake128_init(void);

void libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice data0,
    Eurydice_slice data1);

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out0,
    Eurydice_slice out1);

void libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out0,
    Eurydice_slice out1);

void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data);

void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_neon_H_DEFINED
#endif
