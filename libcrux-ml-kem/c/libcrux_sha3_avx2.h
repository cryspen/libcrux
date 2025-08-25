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


#ifndef __libcrux_sha3_avx2_H
#define __libcrux_sha3_avx2_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "intrinsics/libcrux_intrinsics_avx2.h"

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types core_core_arch_x86___m256i
with const generics
- $4size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_55_s { __m256i st[25U]; }
libcrux_sha3_generic_keccak_KeccakState_55;

/**
 Perform 4 SHAKE256 operations in parallel
*/
void
libcrux_sha3_avx2_x4_shake256(
  Eurydice_slice input0,
  Eurydice_slice input1,
  Eurydice_slice input2,
  Eurydice_slice input3,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

/**
 Initialise the [`KeccakState`].
*/
libcrux_sha3_generic_keccak_KeccakState_55 libcrux_sha3_avx2_x4_incremental_init(void);

/**
 Absorb
*/
void
libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice data0,
  Eurydice_slice data1,
  Eurydice_slice data2,
  Eurydice_slice data3
);

/**
 Squeeze three blocks
*/
void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

/**
 Squeeze another block
*/
void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

/**
 Squeeze five blocks
*/
void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

/**
 Absorb
*/
void
libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice data0,
  Eurydice_slice data1,
  Eurydice_slice data2,
  Eurydice_slice data3
);

/**
 Squeeze block
*/
void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

/**
 Squeeze next block
*/
void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
  libcrux_sha3_generic_keccak_KeccakState_55 *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  Eurydice_slice out2,
  Eurydice_slice out3
);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
