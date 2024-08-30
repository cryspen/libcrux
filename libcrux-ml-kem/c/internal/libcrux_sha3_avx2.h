/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: fcdd1852994390db2b6aa780ed8d837fa811167d
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: 7cd7a08d172e1715493176358bffadf8f87ae3a4
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

typedef libcrux_sha3_generic_keccak_KeccakState_29
    libcrux_sha3_avx2_x4_incremental_KeccakState;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
