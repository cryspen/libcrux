/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 6b5e110342a771a3e1c739b10294b1778e4be8b4
 * Eurydice: 31be7d65ca5d6acdacfb33652e478d24dd85c1cb
 * Karamel: 3205d3365ea2790b02368f79fcee38e38d0b5908
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 4ad532b206174114dd4140b718e7794a28fc59ee
 */

#ifndef __internal_libcrux_sha3_avx2_H
#define __internal_libcrux_sha3_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_avx2.h"
#include "eurydice_glue.h"
#include "internal/libcrux_core.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_absorb_final_7f(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice last[4U]);

typedef libcrux_sha3_generic_keccak_KeccakState_29
    libcrux_sha3_avx2_x4_incremental_KeccakState;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
void libcrux_sha3_generic_keccak_squeeze_first_three_blocks_ed(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]);

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
