/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a8f2211d1b95e0462a96382023b164a4116c7ca4
 * Eurydice: 60f543ddc60a777138070968daaf7620ec48170d
 * Karamel: 1d81d757d5d9e16dd6463ccc72324e587c707959
 * F*: 7cd06c5562fc47ec14cd35c38034d5558a5ff762
 * Libcrux: 370d71828112dbf0ad53a8995502ff1e5c8a719c
 */

#ifndef __internal_libcrux_sha3_avx2_H
#define __internal_libcrux_sha3_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_avx2.h"
#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"

typedef libcrux_sha3_generic_keccak_KeccakState_55
    libcrux_sha3_avx2_x4_incremental_KeccakState;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
