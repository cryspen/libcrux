/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 87a3a2f19ecd5e9528654a0a884682217559b109
 * Eurydice: 2ca24a2e00b05a7eeef7431e37dd113411191f8b
 * Karamel: e19dc6ee1e907e885c1060dacd3bb9be579493fd
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: ea2eb85cd0521e0ff873b8b4700afa04d76ee187
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
