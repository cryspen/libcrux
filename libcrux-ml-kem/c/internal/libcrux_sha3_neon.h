/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: c66a520f7072006af0071eb517002a73d5f3a7d1
 * Eurydice: 9dae7cbf24d38b7b0eb8e7efd12d662a4ebe1f1a
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: fba8ff3916a9aa0a3869f2fffea66d8aea07144a
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
