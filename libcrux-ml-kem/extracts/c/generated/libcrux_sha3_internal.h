/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 0b834617366280f902ccc302d8920f2d508fba45
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 3820cfd1cfca2935e0c8da6a75c5a64ba0911e58
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
