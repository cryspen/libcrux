/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 564ce891b07fd4aefe7d5ccd78e61400b4ac4a2b
 * Karamel: 06a6d2fb3a547d11c9f6dbec26f1f9b5e0dbf411
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#ifndef libcrux_sha3_avx2_H
#define libcrux_sha3_avx2_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "intrinsics/libcrux_intrinsics_avx2.h"

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_05_s {
  __m256i data[25U];
} Eurydice_arr_05;

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
Eurydice_arr_05 libcrux_sha3_avx2_x4_incremental_init(void);

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    Eurydice_arr_05 *s, Eurydice_slice data0, Eurydice_slice data1,
    Eurydice_slice data2, Eurydice_slice data3);

/**
 Squeeze three blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze another block
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze five blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3);

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    Eurydice_arr_05 *s, Eurydice_slice data0, Eurydice_slice data1,
    Eurydice_slice data2, Eurydice_slice data3);

/**
 Squeeze block
*/
void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3);

/**
 Squeeze next block
*/
void libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3);

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_avx2_H_DEFINED
#endif /* libcrux_sha3_avx2_H */
