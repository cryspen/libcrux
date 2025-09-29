/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3275bf4ad9dc8c25965dc5da6122653fc43c4287
 * Eurydice: d3b14228e2b5fe8710ec7efae31e4de2c96ed20d
 * Karamel: 095cdb73f246711f93f99a159ceca37cd2c227e1
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 2c2ff0e7ab8a33ae4dd193d06cd3eaa3bc9f75ab
 */

#ifndef internal_libcrux_sha3_internal_H
#define internal_libcrux_sha3_internal_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_internal.h"

typedef uint8_t libcrux_sha3_Sha3_512Digest[64U];

typedef uint8_t libcrux_sha3_Sha3_384Digest[48U];

typedef uint8_t libcrux_sha3_Sha3_256Digest[32U];

typedef uint8_t libcrux_sha3_Sha3_224Digest[28U];

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_sha3_internal_H_DEFINED
#endif /* internal_libcrux_sha3_internal_H */
