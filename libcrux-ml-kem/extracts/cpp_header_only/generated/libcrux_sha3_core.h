/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 1a15deb0a4af5c10c90c974891a6300b57adef8b
 * Karamel: d55e3f86aa758514f610dfe74f4f1807cdc7244f
 * F*: unset
 * Libcrux: 7627a1f4e6a01f57af3e70129ffa06d3d8e5db72
 */

#ifndef libcrux_sha3_core_H
#define libcrux_sha3_core_H

#include "eurydice_glue.h"

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_a7_s {
  uint64_t data[24U];
} Eurydice_arr_a7;

#define LIBCRUX_SHA3_GENERIC_KECCAK_CONSTANTS_ROUNDCONSTANTS \
  ((Eurydice_arr_a7{{1ULL,                                   \
                     32898ULL,                               \
                     9223372036854808714ULL,                 \
                     9223372039002292224ULL,                 \
                     32907ULL,                               \
                     2147483649ULL,                          \
                     9223372039002292353ULL,                 \
                     9223372036854808585ULL,                 \
                     138ULL,                                 \
                     136ULL,                                 \
                     2147516425ULL,                          \
                     2147483658ULL,                          \
                     2147516555ULL,                          \
                     9223372036854775947ULL,                 \
                     9223372036854808713ULL,                 \
                     9223372036854808579ULL,                 \
                     9223372036854808578ULL,                 \
                     9223372036854775936ULL,                 \
                     32778ULL,                               \
                     9223372039002259466ULL,                 \
                     9223372039002292353ULL,                 \
                     9223372036854808704ULL,                 \
                     2147483649ULL,                          \
                     9223372039002292232ULL}}))

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_c0_s {
  __m256i data[5U];
} Eurydice_arr_c0;

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_05_s {
  __m256i data[25U];
} Eurydice_arr_05;

#define libcrux_sha3_core_H_DEFINED
#endif /* libcrux_sha3_core_H */
