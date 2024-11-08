/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3a133fe0eee9bd3928d5bb16c24ddd2dd0f3ee7f
 * Eurydice: 1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c
 * Karamel: c31a22c1e07d2118c07ee5cebb640d863e31a198
 * F*: 2c32d6e230851bbceadac7a21fc418fa2bb7e4bc
 * Libcrux: 4996d487b60ebd3e41551da8c2a59653beadcb77
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

typedef libcrux_sha3_generic_keccak_KeccakState_55
    libcrux_sha3_avx2_x4_incremental_KeccakState;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
