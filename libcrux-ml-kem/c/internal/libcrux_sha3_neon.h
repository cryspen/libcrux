/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9b87e8727803cd306b94c18b0ceb0b5b1c18c0e9
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */


#ifndef internal_libcrux_sha3_neon_H
#define internal_libcrux_sha3_neon_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"
#include "../libcrux_sha3_neon.h"

/**
A monomorphic instance of Eurydice.arr
with types libcrux_sha3_neon_x2_incremental_KeccakState
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_54_s { Eurydice_arr_fe data[2U]; } Eurydice_arr_54;

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_sha3_neon_H_DEFINED
#endif /* internal_libcrux_sha3_neon_H */
