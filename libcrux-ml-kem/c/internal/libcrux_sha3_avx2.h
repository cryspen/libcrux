/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: ab466d75991f78bb7925bf97c8ee9874f67074f5
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 3339f719293e3d7a5747f6f6c8fecf56f308e0b6
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

typedef libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
    libcrux_sha3_avx2_x4_incremental_KeccakState;

void libcrux_sha3_generic_keccak_absorb_final__core_core_arch_x86___m256i_4size_t_168size_t_31uint8_t(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
        *s,
    Eurydice_slice last[4U]);

void libcrux_sha3_generic_keccak_squeeze_first_three_blocks__core_core_arch_x86___m256i_4size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakState__core_core_arch_x86___m256i__4size_t
        *s,
    Eurydice_slice out[4U]);

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
