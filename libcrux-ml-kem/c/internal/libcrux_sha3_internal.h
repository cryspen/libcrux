/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: ac1a7e957d0dbcab6ae1a948e08b7a16b557851d
 * Karamel: 354791911c6b40d15a41cda7a0e3560da1cf31a1
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: d21c4cc2a58bda0db52962f7b838e8bde470f16b
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
