/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 4d6cf6308cb714aadcd1df0ba5f71977ec6c4a99
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: c9c098bdea22047a1eb811ddf3468543855da224
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

typedef struct
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t_s {
  core_core_arch_x86___m256i st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t;

void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3);

libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
libcrux_sha3_avx2_x4_incremental_shake128_init(void);

void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
        *s,
    Eurydice_slice data0, Eurydice_slice data1, Eurydice_slice data2,
    Eurydice_slice data3);

void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
        *s,
    Eurydice_slice out0, Eurydice_slice out1, Eurydice_slice out2,
    Eurydice_slice out3);

void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
        *s,
    Eurydice_slice out0, Eurydice_slice out1, Eurydice_slice out2,
    Eurydice_slice out3);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
