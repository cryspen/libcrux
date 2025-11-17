/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 146b7dce58cb11ca8010b1c947c3437a959dcd88
 * Eurydice: cdf02f9d8ed0d73f88c0a495c5b79359a51398fc
 * Karamel: 8e7262955105599e91f3a99c9ab3d3387f7046f2
 * F*: unset
 * Libcrux: aef4b0d98bf3abe09b6ac696f60342e2979bb35e
 */

#ifndef libcrux_intrinsics_avx2_H
#define libcrux_intrinsics_avx2_H

#include "eurydice_glue.h"
#include "libcrux_mldsa_core.h"

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

#define libcrux_intrinsics_avx2_H_DEFINED
#endif /* libcrux_intrinsics_avx2_H */
