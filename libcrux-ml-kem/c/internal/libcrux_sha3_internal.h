/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 5807deab3f588567f00046b8ee83e4eba7cff5f6
 * Eurydice: 924e44f2e6e8caac37cddca618ba9488f0990ccc
 * Karamel: c56e0932f05c89c8c68089d909ad9c195f44a02c
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: 85ef3af5e4511668b215821a564d6537be61d44c
 */


#ifndef __internal_libcrux_sha3_internal_H
#define __internal_libcrux_sha3_internal_H

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

#define __internal_libcrux_sha3_internal_H_DEFINED
#endif
