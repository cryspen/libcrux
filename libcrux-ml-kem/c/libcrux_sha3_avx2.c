/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: d6e4d1bb9c27c4eebbebcb29ba8bea1d58741421
 * Karamel: 2bd16e63cfbfa2b81d3c45d597b811ca2a12d430
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: a7de672380a622d67efb35e3707a528e375cbf76
 */

#include "libcrux_sha3_avx2.h"

/**
 Perform 4 SHAKE256 operations in parallel
*/
void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Initialise the [`KeccakState`].
*/
libcrux_sha3_avx2_x4_incremental_KeccakState
libcrux_sha3_avx2_x4_incremental_init(void) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze another block
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze three blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze five blocks
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Absorb
*/
KRML_MUSTINLINE void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze next block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_avx2_x4_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}
