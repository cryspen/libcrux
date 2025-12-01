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

#ifndef libcrux_sha3_internal_H
#define libcrux_sha3_internal_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define libcrux_sha3_Algorithm_Sha224 1
#define libcrux_sha3_Algorithm_Sha256 2
#define libcrux_sha3_Algorithm_Sha384 3
#define libcrux_sha3_Algorithm_Sha512 4

typedef uint8_t libcrux_sha3_Algorithm;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[32U];
} Eurydice_arr_60;

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_internal_H_DEFINED
#endif /* libcrux_sha3_internal_H */
