/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 82bef284a4b2bd383048a1459758e605c976ff11
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: 16f49de38d3b626c0a336b5e2fceb0bf1fed20bf
 */

#ifndef internal_libcrux_sha3_neon_H
#define internal_libcrux_sha3_neon_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_neon.h"
#include "libcrux_core.h"

/**
A monomorphic instance of Eurydice.arr
with types libcrux_sha3_neon_x2_incremental_KeccakState
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_54_s {
  Eurydice_arr_fe data[2U];
} Eurydice_arr_54;

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_sha3_neon_H_DEFINED
#endif /* internal_libcrux_sha3_neon_H */
