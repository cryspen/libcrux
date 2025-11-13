/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: aa8de1a51675fbf6b65135d38d7e3986cadc626f
 * Eurydice: 5dbfcfb3f8f694a4b23d120d18400692e22050d5
 * Karamel: 46bbe26187c3d295b0d78152b6ea447aaf32dac8
 * F*: unset
 * Libcrux: 55a15c0abfa4a1326744575999e590ebcd72ec30
 */

#ifndef libcrux_sha3_internal_H
#define libcrux_sha3_internal_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[32U];
} Eurydice_arr_60;

#define libcrux_sha3_Algorithm_Sha224 1
#define libcrux_sha3_Algorithm_Sha256 2
#define libcrux_sha3_Algorithm_Sha384 3
#define libcrux_sha3_Algorithm_Sha512 4

typedef uint8_t libcrux_sha3_Algorithm;

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_internal_H_DEFINED
#endif /* libcrux_sha3_internal_H */
