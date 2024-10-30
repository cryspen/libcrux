/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 2b71c3c42337fe17ceca860bedaafb3443e6c5e8
 * Eurydice: dcfae68c874635956f71d4c05928841b29ad0a8b
 * Karamel: 87384b244a98a0c41a2e14c65b872d885af7c8df
 * F*: 8b6fce63ca91b16386d8f76e82ea87a3c109a208
 * Libcrux: 4b0d78759e0adf160bab80862883bd5ba7338977
 */

#ifndef __libcrux_sha3_avx2_H
#define __libcrux_sha3_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_core.h"
#include "libcrux_sha3_internal.h"

/**
 Perform 4 SHAKE256 operations in parallel
*/
void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3);

/**
 Initialise the [`KeccakState`].
*/
libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_avx2_x4_incremental_init(void);

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3);

/**
 Squeeze three blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze another block
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze five blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3);

/**
 Squeeze block
*/
void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze next block
*/
void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
