/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9b87e8727803cd306b94c18b0ceb0b5b1c18c0e9
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */


#ifndef libcrux_sha3_neon_H
#define libcrux_sha3_neon_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "intrinsics/libcrux_intrinsics_arm64.h"

#include "libcrux_core.h"

/**
 A SHA3 512 implementation.
*/
void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data);

/**
 A SHA3 256 implementation.
*/
void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data);

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
void
libcrux_sha3_neon_x2_shake256(
  Eurydice_slice input0,
  Eurydice_slice input1,
  Eurydice_slice out0,
  Eurydice_slice out1
);

/**
 Initialise the `KeccakState2`.
*/
Eurydice_arr_fe libcrux_sha3_neon_x2_incremental_init(void);

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
  Eurydice_arr_fe *s,
  Eurydice_slice data0,
  Eurydice_slice data1
);

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
);

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
);

/**
 A SHA3 224 implementation.
*/
void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data);

/**
 A SHA3 384 implementation.
*/
void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data);

/**
 Squeeze five blocks
*/
void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_five_blocks(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
);

/**
 Shake256 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void
libcrux_sha3_neon_x2_incremental_shake256_absorb_final(
  Eurydice_arr_fe *s,
  Eurydice_slice data0,
  Eurydice_slice data1
);

/**
 Squeeze block
*/
void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_first_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
);

/**
 Squeeze next block
*/
void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_next_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
);

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_neon_H_DEFINED
#endif /* libcrux_sha3_neon_H */
