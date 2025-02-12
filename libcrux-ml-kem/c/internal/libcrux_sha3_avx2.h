/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 30cab88265206f4fa849736e704983e39a404d96
 * Eurydice: b8ea420ccde8db516ced5db9c097d77fa558fb94
 * Karamel: 97a06e07e7e423df192c40d5a88bf6c85fd4d278
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: 15b22d1beea1cc7052b8a68b653b012241724664
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
