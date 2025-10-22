/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: unset
 * Libcrux: bccb526ae5d7c8a8845745889b8996dfe9917915
 */

#ifndef libcrux_mlkem768_avx2_H
#define libcrux_mlkem768_avx2_H

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_ct_ops.h"
#include "libcrux_mlkem768_portable.h"
#include "libcrux_mlkem_core.h"
#include "libcrux_sha3_avx2.h"
#include "libcrux_sha3_portable.h"

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_sha3_portable_sha512(output, input);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_sha3_portable_sha256(output, input);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  uint8_t dummy0[192U] = {0U};
  uint8_t dummy1[192U] = {0U};
  switch ((uint8_t)Eurydice_slice_len(input, uint8_t[33U])) {
    case 2U: {
      Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at_mut(
          outputs, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out0 = uu____0.fst;
      Eurydice_slice out1 = uu____0.snd;
      Eurydice_slice uu____1 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____2 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)1U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____3 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____4 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____5 = out0;
      Eurydice_slice uu____6 = out1;
      Eurydice_slice uu____7 = Eurydice_array_to_subslice_to(
          (size_t)192U, dummy0, out_len, uint8_t, size_t, uint8_t[]);
      libcrux_sha3_avx2_x4_shake256(
          uu____1, uu____2, uu____3, uu____4, uu____5, uu____6, uu____7,
          Eurydice_array_to_subslice_to((size_t)192U, dummy1, out_len, uint8_t,
                                        size_t, uint8_t[]));
      break;
    }
    case 3U: {
      Eurydice_slice_uint8_t_x2 uu____8 = Eurydice_slice_split_at_mut(
          outputs, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out0 = uu____8.fst;
      Eurydice_slice rest = uu____8.snd;
      Eurydice_slice_uint8_t_x2 uu____9 = Eurydice_slice_split_at_mut(
          rest, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out1 = uu____9.fst;
      Eurydice_slice out2 = uu____9.snd;
      Eurydice_slice uu____10 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____11 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)1U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____12 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)2U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____13 = Eurydice_array_to_slice(
          (size_t)33U,
          Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                               uint8_t(*)[33U]),
          uint8_t);
      Eurydice_slice uu____14 = out0;
      Eurydice_slice uu____15 = out1;
      Eurydice_slice uu____16 = out2;
      libcrux_sha3_avx2_x4_shake256(
          uu____10, uu____11, uu____12, uu____13, uu____14, uu____15, uu____16,
          Eurydice_array_to_subslice_to((size_t)192U, dummy1, out_len, uint8_t,
                                        size_t, uint8_t[]));
      break;
    }
    case 4U: {
      Eurydice_slice_uint8_t_x2 uu____17 = Eurydice_slice_split_at_mut(
          outputs, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out0 = uu____17.fst;
      Eurydice_slice rest0 = uu____17.snd;
      Eurydice_slice_uint8_t_x2 uu____18 = Eurydice_slice_split_at_mut(
          rest0, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out1 = uu____18.fst;
      Eurydice_slice rest = uu____18.snd;
      Eurydice_slice_uint8_t_x2 uu____19 = Eurydice_slice_split_at_mut(
          rest, out_len, uint8_t, Eurydice_slice_uint8_t_x2);
      Eurydice_slice out2 = uu____19.fst;
      Eurydice_slice out3 = uu____19.snd;
      libcrux_sha3_avx2_x4_shake256(
          Eurydice_array_to_slice(
              (size_t)33U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[33U],
                                   uint8_t(*)[33U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)33U,
              Eurydice_slice_index(input, (size_t)1U, uint8_t[33U],
                                   uint8_t(*)[33U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)33U,
              Eurydice_slice_index(input, (size_t)2U, uint8_t[33U],
                                   uint8_t(*)[33U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)33U,
              Eurydice_slice_index(input, (size_t)3U, uint8_t[33U],
                                   uint8_t(*)[33U]),
              uint8_t),
          out0, out1, out2, out3);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final(
    Eurydice_slice input) {
  libcrux_sha3_generic_keccak_KeccakState_55 state =
      libcrux_sha3_avx2_x4_incremental_init();
  switch ((uint8_t)Eurydice_slice_len(input, uint8_t[34U])) {
    case 2U: {
      libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
          &state,
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)1U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t));
      break;
    }
    case 3U: {
      libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
          &state,
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)1U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)2U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t));
      break;
    }
    case 4U: {
      libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
          &state,
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)0U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)1U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)2U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t),
          Eurydice_array_to_slice(
              (size_t)34U,
              Eurydice_slice_index(input, (size_t)3U, uint8_t[34U],
                                   uint8_t(*)[34U]),
              uint8_t));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  return state;
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *st, Eurydice_slice outputs) {
  uint8_t out0[504U] = {0U};
  uint8_t out1[504U] = {0U};
  uint8_t out2[504U] = {0U};
  uint8_t out3[504U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
      st, Eurydice_array_to_slice((size_t)504U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)504U, out3, uint8_t));
  switch ((uint8_t)Eurydice_slice_len(outputs, uint8_t[504U])) {
    case 2U: {
      uint8_t uu____0[504U];
      memcpy(uu____0, out0, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____0, (size_t)504U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out1[504U];
      memcpy(copy_of_out1, out1, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             copy_of_out1, (size_t)504U * sizeof(uint8_t));
      break;
    }
    case 3U: {
      uint8_t uu____2[504U];
      memcpy(uu____2, out0, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____2, (size_t)504U * sizeof(uint8_t));
      uint8_t uu____3[504U];
      memcpy(uu____3, out1, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____3, (size_t)504U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out2[504U];
      memcpy(copy_of_out2, out2, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)2U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             copy_of_out2, (size_t)504U * sizeof(uint8_t));
      break;
    }
    case 4U: {
      uint8_t uu____5[504U];
      memcpy(uu____5, out0, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____5, (size_t)504U * sizeof(uint8_t));
      uint8_t uu____6[504U];
      memcpy(uu____6, out1, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____6, (size_t)504U * sizeof(uint8_t));
      uint8_t uu____7[504U];
      memcpy(uu____7, out2, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)2U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             uu____7, (size_t)504U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out3[504U];
      memcpy(copy_of_out3, out3, (size_t)504U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)3U, uint8_t[504U],
                                  uint8_t(*)[504U]),
             copy_of_out3, (size_t)504U * sizeof(uint8_t));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *st, Eurydice_slice outputs) {
  uint8_t out0[168U] = {0U};
  uint8_t out1[168U] = {0U};
  uint8_t out2[168U] = {0U};
  uint8_t out3[168U] = {0U};
  libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
      st, Eurydice_array_to_slice((size_t)168U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  switch ((uint8_t)Eurydice_slice_len(outputs, uint8_t[168U])) {
    case 2U: {
      uint8_t uu____0[168U];
      memcpy(uu____0, out0, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____0, (size_t)168U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out1[168U];
      memcpy(copy_of_out1, out1, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             copy_of_out1, (size_t)168U * sizeof(uint8_t));
      break;
    }
    case 3U: {
      uint8_t uu____2[168U];
      memcpy(uu____2, out0, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____2, (size_t)168U * sizeof(uint8_t));
      uint8_t uu____3[168U];
      memcpy(uu____3, out1, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____3, (size_t)168U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out2[168U];
      memcpy(copy_of_out2, out2, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)2U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             copy_of_out2, (size_t)168U * sizeof(uint8_t));
      break;
    }
    case 4U: {
      uint8_t uu____5[168U];
      memcpy(uu____5, out0, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)0U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____5, (size_t)168U * sizeof(uint8_t));
      uint8_t uu____6[168U];
      memcpy(uu____6, out1, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)1U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____6, (size_t)168U * sizeof(uint8_t));
      uint8_t uu____7[168U];
      memcpy(uu____7, out2, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)2U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             uu____7, (size_t)168U * sizeof(uint8_t));
      /* Passing arrays by value in Rust generates a copy in C */
      uint8_t copy_of_out3[168U];
      memcpy(copy_of_out3, out3, (size_t)168U * sizeof(uint8_t));
      memcpy(Eurydice_slice_index(outputs, (size_t)3U, uint8_t[168U],
                                  uint8_t(*)[168U]),
             copy_of_out3, (size_t)168U * sizeof(uint8_t));
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_G_26(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_avx2_G(input, output);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_H_26(
    Eurydice_slice input, Eurydice_slice output) {
  libcrux_ml_kem_hash_functions_avx2_H(input, output);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRFxN_26(
    Eurydice_slice input, Eurydice_slice outputs, size_t out_len) {
  libcrux_ml_kem_hash_functions_avx2_PRFxN(input, outputs, out_len);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_26(
    Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final(input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_26(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice outputs) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks(
      self, outputs);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_26(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice outputs) {
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block(self, outputs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_vec_zero(void) {
  return libcrux_intrinsics_avx2_mm256_setzero_si256();
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_ml_kem_vector_avx2_ZERO_f5(void) {
  return libcrux_ml_kem_vector_avx2_vec_zero();
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_vec_from_i16_array(
    Eurydice_slice array, __m256i *out) {
  out[0U] = libcrux_intrinsics_avx2_mm256_loadu_si256_i16(array);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_from_i16_array_f5(
    Eurydice_slice array, __m256i *out) {
  libcrux_ml_kem_vector_avx2_vec_from_i16_array(array, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_arithmetic_add(
    __m256i *lhs, __m256i *rhs) {
  lhs[0U] = libcrux_intrinsics_avx2_mm256_add_epi16(lhs[0U], rhs[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_add_f5(__m256i *lhs,
                                                              __m256i *rhs) {
  libcrux_ml_kem_vector_avx2_arithmetic_add(lhs, rhs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_arithmetic_sub(
    __m256i *lhs, __m256i *rhs) {
  lhs[0U] = libcrux_intrinsics_avx2_mm256_sub_epi16(lhs[0U], rhs[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_sub_f5(__m256i *lhs,
                                                              __m256i *rhs) {
  libcrux_ml_kem_vector_avx2_arithmetic_sub(lhs, rhs);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_arithmetic_negate(
    __m256i *vec) {
  vec[0U] = libcrux_intrinsics_avx2_mm256_sign_epi16(
      vec[0U], libcrux_intrinsics_avx2_mm256_set1_epi16((int16_t)-1));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_negate_f5(__m256i *vec) {
  libcrux_ml_kem_vector_avx2_arithmetic_negate(vec);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(__m256i *vector,
                                                           int16_t constant) {
  __m256i cv = libcrux_intrinsics_avx2_mm256_set1_epi16(constant);
  __m256i result = libcrux_intrinsics_avx2_mm256_mullo_epi16(vector[0U], cv);
  vector[0U] = result;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_multiply_by_constant_f5(
    __m256i *vec, int16_t c) {
  libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(vec, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant) {
  __m256i cv = libcrux_intrinsics_avx2_mm256_set1_epi16(constant);
  return libcrux_intrinsics_avx2_mm256_and_si256(vector, cv);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_f5(__m256i *vec,
                                                        int16_t c) {
  vec[0U] = libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      vec[0U], c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(__m256i *vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i v_minus_field_modulus =
      libcrux_intrinsics_avx2_mm256_sub_epi16(vector[0U], field_modulus);
  __m256i sign_mask = libcrux_intrinsics_avx2_mm256_srai_epi16(
      (int32_t)15, v_minus_field_modulus, __m256i);
  __m256i conditional_add_field_modulus =
      libcrux_intrinsics_avx2_mm256_and_si256(sign_mask, field_modulus);
  __m256i result = libcrux_intrinsics_avx2_mm256_add_epi16(
      v_minus_field_modulus, conditional_add_field_modulus);
  vector[0U] = result;
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_cond_subtract_3329(
    __m256i *vector) {
  libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_cond_subtract_3329_f5(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_cond_subtract_3329(vec);
}

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i *vector) {
  __m256i t0 = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      vector[0U],
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER));
  __m256i t512 = libcrux_intrinsics_avx2_mm256_set1_epi16((int16_t)512);
  __m256i t1 = libcrux_intrinsics_avx2_mm256_add_epi16(t0, t512);
  __m256i quotient =
      libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)10, t1, __m256i);
  __m256i quotient_times_field_modulus =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(
          quotient, libcrux_intrinsics_avx2_mm256_set1_epi16(
                        LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i result = libcrux_intrinsics_avx2_mm256_sub_epi16(
      vector[0U], quotient_times_field_modulus);
  vector[0U] = result;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_barrett_reduce_f5(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(vec);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i *vector, int16_t constant) {
  __m256i vec_constant = libcrux_intrinsics_avx2_mm256_set1_epi16(constant);
  __m256i value_low =
      libcrux_intrinsics_avx2_mm256_mullo_epi16(vector[0U], vec_constant);
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(k, modulus);
  __m256i value_high =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(vector[0U], vec_constant);
  __m256i result =
      libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
  vector[0U] = result;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(__m256i *vec,
                                                              int16_t c) {
  libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(vec, c);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_shift_right_ef(__m256i vector) {
  return libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, vector, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_to_unsigned_representative(__m256i a) {
  __m256i t = libcrux_ml_kem_vector_avx2_arithmetic_shift_right_ef(a);
  __m256i fm = libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
      t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  libcrux_ml_kem_vector_avx2_arithmetic_add(&a, &fm);
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(__m256i vec) {
  return libcrux_ml_kem_vector_avx2_arithmetic_to_unsigned_representative(vec);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    __m256i *vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)2);
  __m256i field_modulus_quartered = libcrux_intrinsics_avx2_mm256_set1_epi16(
      (LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int16_t)1) / (int16_t)4);
  __m256i shifted =
      libcrux_intrinsics_avx2_mm256_sub_epi16(field_modulus_halved, vector[0U]);
  __m256i mask =
      libcrux_intrinsics_avx2_mm256_srai_epi16((int32_t)15, shifted, __m256i);
  __m256i shifted_to_positive =
      libcrux_intrinsics_avx2_mm256_xor_si256(mask, shifted);
  __m256i shifted_to_positive_in_range =
      libcrux_intrinsics_avx2_mm256_sub_epi16(shifted_to_positive,
                                              field_modulus_quartered);
  vector[0U] = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)15, shifted_to_positive_in_range, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_1(
    __m256i *vector) {
  libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_1_f5(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_compress_1(vec);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(__m256i lhs,
                                                      __m256i rhs) {
  __m256i prod02 = libcrux_intrinsics_avx2_mm256_mul_epu32(lhs, rhs);
  __m256i prod13 = libcrux_intrinsics_avx2_mm256_mul_epu32(
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, lhs, __m256i),
      libcrux_intrinsics_avx2_mm256_shuffle_epi32((int32_t)245, rhs, __m256i));
  return libcrux_intrinsics_avx2_mm256_unpackhi_epi64(
      libcrux_intrinsics_avx2_mm256_unpacklo_epi32(prod02, prod13),
      libcrux_intrinsics_avx2_mm256_unpackhi_epi32(prod02, prod13));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    __m256i vec, __m256i constants) {
  __m256i value_low = libcrux_intrinsics_avx2_mm256_mullo_epi16(vec, constants);
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm256_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i k_times_modulus =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(k, modulus);
  __m256i value_high =
      libcrux_intrinsics_avx2_mm256_mulhi_epi16(vec, constants);
  return libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1,
      -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)245, vector[0U], __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)160, vector[0U], __m256i);
  vector[0U] = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_1_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(vector, zeta0, zeta1, zeta2,
                                                  zeta3);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_1_step_f5(
    __m256i *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_ntt_layer_1_step(vec, zeta0, zeta1, zeta2, zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1) {
  __m256i zetas = libcrux_intrinsics_avx2_mm256_set_epi16(
      -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0,
      -zeta0, -zeta0, -zeta0, zeta0, zeta0, zeta0, zeta0);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)238, vector[0U], __m256i);
  __m256i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          rhs, zetas);
  __m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)68, vector[0U], __m256i);
  vector[0U] = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_2_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(vector, zeta0, zeta1);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_2_step_f5(
    __m256i *vec, int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_avx2_ntt_layer_2_step(vec, zeta0, zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    __m128i vec, __m128i constants) {
  __m128i value_low = libcrux_intrinsics_avx2_mm_mullo_epi16(vec, constants);
  __m128i k = libcrux_intrinsics_avx2_mm_mullo_epi16(
      value_low,
      libcrux_intrinsics_avx2_mm_set1_epi16(
          (int16_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m128i modulus = libcrux_intrinsics_avx2_mm_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m128i k_times_modulus = libcrux_intrinsics_avx2_mm_mulhi_epi16(k, modulus);
  __m128i value_high = libcrux_intrinsics_avx2_mm_mulhi_epi16(vec, constants);
  return libcrux_intrinsics_avx2_mm_sub_epi16(value_high, k_times_modulus);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(
    __m256i *vector, int16_t zeta) {
  __m128i rhs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m128i rhs0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          rhs, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  __m128i lhs = libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs0);
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs0);
  vector[0U] =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  vector[0U] = libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, vector[0U], upper_coefficients, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_3_step(
    __m256i *vector, int16_t zeta) {
  libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(vector, zeta);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_layer_3_step_f5(
    __m256i *vec, int16_t zeta0) {
  libcrux_ml_kem_vector_avx2_ntt_layer_3_step(vec, zeta0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  __m256i lhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)245, vector[0U], __m256i);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_shuffle_epi32(
      (int32_t)160, vector[0U], __m256i);
  __m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1,
               (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1));
  __m256i sum = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum, libcrux_intrinsics_avx2_mm256_set_epi16(
                   zeta3, zeta3, (int16_t)0, (int16_t)0, zeta2, zeta2,
                   (int16_t)0, (int16_t)0, zeta1, zeta1, (int16_t)0, (int16_t)0,
                   zeta0, zeta0, (int16_t)0, (int16_t)0));
  libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(&sum);
  vector[0U] = libcrux_intrinsics_avx2_mm256_blend_epi16(
      (int32_t)204, sum, sum_times_zetas, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(vector, zeta0, zeta1,
                                                      zeta2, zeta3);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_f5(
    __m256i *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step(vec, zeta0, zeta1, zeta2,
                                                  zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1) {
  __m256i lhs = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)245, vector[0U], __m256i);
  __m256i rhs = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)160, vector[0U], __m256i);
  __m256i rhs0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      rhs, libcrux_intrinsics_avx2_mm256_set_epi16(
               (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)-1, (int16_t)1,
               (int16_t)1, (int16_t)1, (int16_t)1, (int16_t)-1, (int16_t)-1,
               (int16_t)-1, (int16_t)-1, (int16_t)1, (int16_t)1, (int16_t)1,
               (int16_t)1));
  __m256i sum = libcrux_intrinsics_avx2_mm256_add_epi16(lhs, rhs0);
  __m256i sum_times_zetas =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
          sum, libcrux_intrinsics_avx2_mm256_set_epi16(
                   zeta1, zeta1, zeta1, zeta1, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, zeta0, zeta0, zeta0, zeta0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0));
  vector[0U] = libcrux_intrinsics_avx2_mm256_blend_epi16(
      (int32_t)240, sum, sum_times_zetas, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step(
    __m256i *vector, int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(vector, zeta0, zeta1);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_f5(
    __m256i *vec, int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step(vec, zeta0, zeta1);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(
    __m256i *vector, int16_t zeta) {
  __m128i lhs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m128i rhs = libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_add_epi16(lhs, rhs);
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_sub_epi16(lhs, rhs);
  __m128i upper_coefficients0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
          upper_coefficients, libcrux_intrinsics_avx2_mm_set1_epi16(zeta));
  vector[0U] =
      libcrux_intrinsics_avx2_mm256_castsi128_si256(lower_coefficients);
  vector[0U] = libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, vector[0U], upper_coefficients0, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step(
    __m256i *vector, int16_t zeta) {
  libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(vector, zeta);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_f5(
    __m256i *vec, int16_t zeta0) {
  libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step(vec, zeta0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(__m256i vec) {
  __m256i k = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      vec,
      libcrux_intrinsics_avx2_mm256_set1_epi32(
          (int32_t)
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  __m256i k_times_modulus = libcrux_intrinsics_avx2_mm256_mulhi_epi16(
      k, libcrux_intrinsics_avx2_mm256_set1_epi32(
             (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  __m256i value_high =
      libcrux_intrinsics_avx2_mm256_srli_epi32((int32_t)16, vec, __m256i);
  __m256i result =
      libcrux_intrinsics_avx2_mm256_sub_epi16(value_high, k_times_modulus);
  __m256i result0 =
      libcrux_intrinsics_avx2_mm256_slli_epi32((int32_t)16, result, __m256i);
  return libcrux_intrinsics_avx2_mm256_srai_epi32((int32_t)16, result0,
                                                  __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(
    __m256i *lhs, __m256i *rhs, __m256i *out, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  __m256i shuffle_with = libcrux_intrinsics_avx2_mm256_set_epi8(
      (int8_t)15, (int8_t)14, (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6,
      (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8,
      (int8_t)5, (int8_t)4, (int8_t)1, (int8_t)0, (int8_t)15, (int8_t)14,
      (int8_t)11, (int8_t)10, (int8_t)7, (int8_t)6, (int8_t)3, (int8_t)2,
      (int8_t)13, (int8_t)12, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
      (int8_t)1, (int8_t)0);
  __m256i lhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(lhs[0U], shuffle_with);
  __m256i lhs_shuffled0 = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, lhs_shuffled, __m256i);
  __m128i lhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(lhs_shuffled0);
  __m256i lhs_evens0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_evens);
  __m128i lhs_odds = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, lhs_shuffled0, __m128i);
  __m256i lhs_odds0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(lhs_odds);
  __m256i rhs_shuffled =
      libcrux_intrinsics_avx2_mm256_shuffle_epi8(rhs[0U], shuffle_with);
  __m256i rhs_shuffled0 = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, rhs_shuffled, __m256i);
  __m128i rhs_evens =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(rhs_shuffled0);
  __m256i rhs_evens0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_evens);
  __m128i rhs_odds = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, rhs_shuffled0, __m128i);
  __m256i rhs_odds0 = libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(rhs_odds);
  __m256i left =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_evens0, rhs_evens0);
  __m256i right =
      libcrux_intrinsics_avx2_mm256_mullo_epi32(lhs_odds0, rhs_odds0);
  __m256i right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(right);
  __m256i right1 = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      right0,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          -(int32_t)zeta3, (int32_t)zeta3, -(int32_t)zeta2, (int32_t)zeta2,
          -(int32_t)zeta1, (int32_t)zeta1, -(int32_t)zeta0, (int32_t)zeta0));
  __m256i products_left = libcrux_intrinsics_avx2_mm256_add_epi32(left, right1);
  __m256i products_left0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_left);
  __m256i rhs_adjacent_swapped = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      rhs[0U],
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)13, (int8_t)12, (int8_t)15, (int8_t)14, (int8_t)9, (int8_t)8,
          (int8_t)11, (int8_t)10, (int8_t)5, (int8_t)4, (int8_t)7, (int8_t)6,
          (int8_t)1, (int8_t)0, (int8_t)3, (int8_t)2, (int8_t)13, (int8_t)12,
          (int8_t)15, (int8_t)14, (int8_t)9, (int8_t)8, (int8_t)11, (int8_t)10,
          (int8_t)5, (int8_t)4, (int8_t)7, (int8_t)6, (int8_t)1, (int8_t)0,
          (int8_t)3, (int8_t)2));
  __m256i products_right =
      libcrux_intrinsics_avx2_mm256_madd_epi16(lhs[0U], rhs_adjacent_swapped);
  __m256i products_right0 =
      libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
          products_right);
  __m256i products_right1 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)16, products_right0, __m256i);
  out[0U] = libcrux_intrinsics_avx2_mm256_blend_epi16(
      (int32_t)170, products_left0, products_right1, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_multiply(
    __m256i *lhs, __m256i *rhs, __m256i *out, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(lhs, rhs, out, zeta0, zeta1,
                                              zeta2, zeta3);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_ntt_multiply_f5(
    __m256i *lhs, __m256i *rhs, __m256i *out, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_avx2_ntt_multiply(lhs, rhs, out, zeta0, zeta1, zeta2,
                                          zeta3);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    __m256i *vector, Eurydice_slice out) {
  __m256i lsb_to_msb = libcrux_intrinsics_avx2_mm256_slli_epi16(
      (int32_t)15, vector[0U], __m256i);
  __m128i low_msbs = libcrux_intrinsics_avx2_mm256_castsi256_si128(lsb_to_msb);
  __m128i high_msbs = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, lsb_to_msb, __m128i);
  __m128i msbs = libcrux_intrinsics_avx2_mm_packs_epi16(low_msbs, high_msbs);
  int32_t bits_packed = libcrux_intrinsics_avx2_mm_movemask_epi8(msbs);
  Eurydice_slice_index(out, (size_t)0U, uint8_t, uint8_t *) =
      (uint8_t)bits_packed;
  Eurydice_slice_index(out, (size_t)1U, uint8_t, uint8_t *) =
      (uint8_t)(bits_packed >> 8U);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_1(
    __m256i *vector, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(vector, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_1_f5(
    __m256i *vec, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_1(vec, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_i16s(
    int16_t a, int16_t b) {
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_set_epi16(
      b, b, b, b, b, b, b, b, a, a, a, a, a, a, a, a);
  __m256i coefficients_in_msb = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi16(
                        (int16_t)1 << 8U, (int16_t)1 << 9U, (int16_t)1 << 10U,
                        (int16_t)1 << 11U, (int16_t)1 << 12U, (int16_t)1 << 13U,
                        (int16_t)1 << 14U, (int16_t)-32768, (int16_t)1 << 8U,
                        (int16_t)1 << 9U, (int16_t)1 << 10U, (int16_t)1 << 11U,
                        (int16_t)1 << 12U, (int16_t)1 << 13U, (int16_t)1 << 14U,
                        (int16_t)-32768));
  return libcrux_intrinsics_avx2_mm256_srli_epi16((int32_t)15,
                                                  coefficients_in_msb, __m256i);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_u8s(
    uint8_t a, uint8_t b) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_i16s(
      (int16_t)a, (int16_t)b);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_deserialize_1(
    Eurydice_slice bytes, __m256i *out) {
  out[0U] =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_u8s(
          Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_1(
    Eurydice_slice bytes, __m256i *out) {
  libcrux_ml_kem_vector_avx2_serialize_deserialize_1(bytes, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_1_f5(
    Eurydice_slice input, __m256i *out) {
  libcrux_ml_kem_vector_avx2_deserialize_1(input, out);
}

/**
 `mm256_concat_pairs_n(n, x)` is then a sequence of 32 bits packets
 of the shape `0b0…0b₁…bₙa₁…aₙ`, if `x` is a sequence of pairs of
 16 bits, of the shape `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)` (where the last
 `n` bits are non-zero).
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(uint8_t n,
                                                          __m256i x) {
  int16_t n0 = (int16_t)1 << (uint32_t)n;
  return libcrux_intrinsics_avx2_mm256_madd_epi16(
      x, libcrux_intrinsics_avx2_mm256_set_epi16(
             n0, (int16_t)1, n0, (int16_t)1, n0, (int16_t)1, n0, (int16_t)1, n0,
             (int16_t)1, n0, (int16_t)1, n0, (int16_t)1, n0, (int16_t)1));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    __m256i *vector, Eurydice_slice out) {
  uint8_t serialized[16U] = {0U};
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(4U, vector[0U]);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_2_combined,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4, (int8_t)0,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)12, (int8_t)8, (int8_t)4, (int8_t)0));
  __m256i combined = libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(
      adjacent_8_combined, libcrux_intrinsics_avx2_mm256_set_epi32(
                               (int32_t)0, (int32_t)0, (int32_t)0, (int32_t)0,
                               (int32_t)0, (int32_t)0, (int32_t)4, (int32_t)0));
  __m128i combined0 = libcrux_intrinsics_avx2_mm256_castsi256_si128(combined);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_slice((size_t)16U, serialized, uint8_t), combined0);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice3(serialized, (size_t)0U,
                                                  (size_t)8U, uint8_t *),
                      uint8_t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_4(
    __m256i *vector, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_4(vector, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_4_f5(
    __m256i *vec, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_4(vec, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_i16s(
    int16_t b0, int16_t b1, int16_t b2, int16_t b3, int16_t b4, int16_t b5,
    int16_t b6, int16_t b7) {
  __m256i coefficients = libcrux_intrinsics_avx2_mm256_set_epi16(
      b7, b7, b6, b6, b5, b5, b4, b4, b3, b3, b2, b2, b1, b1, b0, b0);
  __m256i coefficients_in_msb = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi16(
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U));
  __m256i coefficients_in_lsb = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)4, coefficients_in_msb, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients_in_lsb, libcrux_intrinsics_avx2_mm256_set1_epi16(
                               ((int16_t)1 << 4U) - (int16_t)1));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_u8s(
    uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3, uint8_t b4, uint8_t b5,
    uint8_t b6, uint8_t b7) {
  return libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_i16s(
      (int16_t)b0, (int16_t)b1, (int16_t)b2, (int16_t)b3, (int16_t)b4,
      (int16_t)b5, (int16_t)b6, (int16_t)b7);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_deserialize_4(
    Eurydice_slice bytes, __m256i *out) {
  out[0U] =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_u8s(
          Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *),
          Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_4(
    Eurydice_slice bytes, __m256i *out) {
  libcrux_ml_kem_vector_avx2_serialize_deserialize_4(bytes, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_4_f5(
    Eurydice_slice input, __m256i *out) {
  libcrux_ml_kem_vector_avx2_deserialize_4(input, out);
}

/**
 We cannot model `mm256_inserti128_si256` on its own: it produces a
 Vec256 where the upper 128 bits are undefined. Thus
 `mm256_inserti128_si256` is not pure.

 Luckily, we always call `mm256_castsi128_si256` right after
 `mm256_inserti128_si256`: this composition sets the upper bits,
 making the whole computation pure again.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(__m128i lower,
                                                                __m128i upper) {
  return libcrux_intrinsics_avx2_mm256_inserti128_si256(
      (int32_t)1, libcrux_intrinsics_avx2_mm256_castsi128_si256(lower), upper,
      __m256i);
}

typedef struct core_core_arch_x86___m128i_x2_s {
  __m128i fst;
  __m128i snd;
} core_core_arch_x86___m128i_x2;

KRML_ATTRIBUTE_TARGET("avx2")
static inline core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
    __m256i vector) {
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(10U, vector);
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_2_combined,
      libcrux_intrinsics_avx2_mm256_set_epi32(
          (int32_t)0, (int32_t)12, (int32_t)0, (int32_t)12, (int32_t)0,
          (int32_t)12, (int32_t)0, (int32_t)12));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)12, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_4_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)-1, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8,
          (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1,
          (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)4,
          (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  __m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  __m128i upper_8 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, __m128i);
  return (core_core_arch_x86___m128i_x2{lower_8, upper_8});
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    __m256i *vector, Eurydice_slice out) {
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
          vector[0U]);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  uint8_t serialized[32U] = {0U};
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice3(serialized, (size_t)0U, (size_t)16U,
                                  uint8_t *),
      lower_8);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice3(serialized, (size_t)10U, (size_t)26U,
                                  uint8_t *),
      upper_8);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice3(serialized, (size_t)0U,
                                                  (size_t)20U, uint8_t *),
                      uint8_t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_10(
    __m256i *vector, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_10(vector, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_10_f5(
    __m256i *vec, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_10(vec, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients0,
      libcrux_intrinsics_avx2_mm_set_epi8(
          (int8_t)9, (int8_t)8, (int8_t)8, (int8_t)7, (int8_t)7, (int8_t)6,
          (int8_t)6, (int8_t)5, (int8_t)4, (int8_t)3, (int8_t)3, (int8_t)2,
          (int8_t)2, (int8_t)1, (int8_t)1, (int8_t)0));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients0,
      libcrux_intrinsics_avx2_mm_set_epi8(
          (int8_t)15, (int8_t)14, (int8_t)14, (int8_t)13, (int8_t)13,
          (int8_t)12, (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)9,
          (int8_t)8, (int8_t)8, (int8_t)7, (int8_t)7, (int8_t)6));
  __m256i coefficients =
      libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
          lower_coefficients, upper_coefficients);
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi16(
                        (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
                        (int16_t)1 << 6U, (int16_t)1 << 0U, (int16_t)1 << 2U,
                        (int16_t)1 << 4U, (int16_t)1 << 6U, (int16_t)1 << 0U,
                        (int16_t)1 << 2U, (int16_t)1 << 4U, (int16_t)1 << 6U,
                        (int16_t)1 << 0U, (int16_t)1 << 2U, (int16_t)1 << 4U,
                        (int16_t)1 << 6U));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)6, coefficients0, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients1, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 10U) - (int16_t)1));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_deserialize_10(
    Eurydice_slice bytes, __m256i *out) {
  Eurydice_slice lower_coefficients =
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)16U, uint8_t *);
  Eurydice_slice upper_coefficients =
      Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)20U, uint8_t *);
  out[0U] =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
          libcrux_intrinsics_avx2_mm_loadu_si128(lower_coefficients),
          libcrux_intrinsics_avx2_mm_loadu_si128(upper_coefficients));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_10(
    Eurydice_slice bytes, __m256i *out) {
  libcrux_ml_kem_vector_avx2_serialize_deserialize_10(bytes, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_10_f5(
    Eurydice_slice input, __m256i *out) {
  libcrux_ml_kem_vector_avx2_deserialize_10(input, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
    __m256i vector) {
  __m256i adjacent_2_combined =
      libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(12U, vector);
  __m256i adjacent_4_combined = libcrux_intrinsics_avx2_mm256_sllv_epi32(
      adjacent_2_combined, libcrux_intrinsics_avx2_mm256_set_epi32(
                               (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8,
                               (int32_t)0, (int32_t)8, (int32_t)0, (int32_t)8));
  __m256i adjacent_4_combined0 = libcrux_intrinsics_avx2_mm256_srli_epi64(
      (int32_t)8, adjacent_4_combined, __m256i);
  __m256i adjacent_8_combined = libcrux_intrinsics_avx2_mm256_shuffle_epi8(
      adjacent_4_combined0,
      libcrux_intrinsics_avx2_mm256_set_epi8(
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13,
          (int8_t)12, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)5,
          (int8_t)4, (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0, (int8_t)-1,
          (int8_t)-1, (int8_t)-1, (int8_t)-1, (int8_t)13, (int8_t)12,
          (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)5, (int8_t)4,
          (int8_t)3, (int8_t)2, (int8_t)1, (int8_t)0));
  __m128i lower_8 =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(adjacent_8_combined);
  __m128i upper_8 = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, adjacent_8_combined, __m128i);
  return (core_core_arch_x86___m128i_x2{lower_8, upper_8});
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    __m256i *vector, Eurydice_slice out) {
  uint8_t serialized[32U] = {0U};
  core_core_arch_x86___m128i_x2 uu____0 =
      libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
          vector[0U]);
  __m128i lower_8 = uu____0.fst;
  __m128i upper_8 = uu____0.snd;
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice3(serialized, (size_t)0U, (size_t)16U,
                                  uint8_t *),
      lower_8);
  libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
      Eurydice_array_to_subslice3(serialized, (size_t)12U, (size_t)28U,
                                  uint8_t *),
      upper_8);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice3(serialized, (size_t)0U,
                                                  (size_t)24U, uint8_t *),
                      uint8_t);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_12(
    __m256i *vector, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_serialize_12(vector, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_12_f5(
    __m256i *vec, Eurydice_slice out) {
  libcrux_ml_kem_vector_avx2_serialize_12(vec, out);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0) {
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients0,
      libcrux_intrinsics_avx2_mm_set_epi8(
          (int8_t)11, (int8_t)10, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)7,
          (int8_t)7, (int8_t)6, (int8_t)5, (int8_t)4, (int8_t)4, (int8_t)3,
          (int8_t)2, (int8_t)1, (int8_t)1, (int8_t)0));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients0,
      libcrux_intrinsics_avx2_mm_set_epi8(
          (int8_t)15, (int8_t)14, (int8_t)14, (int8_t)13, (int8_t)12,
          (int8_t)11, (int8_t)11, (int8_t)10, (int8_t)9, (int8_t)8, (int8_t)8,
          (int8_t)7, (int8_t)6, (int8_t)5, (int8_t)5, (int8_t)4));
  __m256i coefficients =
      libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
          lower_coefficients, upper_coefficients);
  __m256i coefficients0 = libcrux_intrinsics_avx2_mm256_mullo_epi16(
      coefficients, libcrux_intrinsics_avx2_mm256_set_epi16(
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U, (int16_t)1 << 0U, (int16_t)1 << 4U,
                        (int16_t)1 << 0U, (int16_t)1 << 4U, (int16_t)1 << 0U,
                        (int16_t)1 << 4U));
  __m256i coefficients1 = libcrux_intrinsics_avx2_mm256_srli_epi16(
      (int32_t)4, coefficients0, __m256i);
  return libcrux_intrinsics_avx2_mm256_and_si256(
      coefficients1, libcrux_intrinsics_avx2_mm256_set1_epi16(
                         ((int16_t)1 << 12U) - (int16_t)1));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_serialize_deserialize_12(
    Eurydice_slice bytes, __m256i *out) {
  __m128i lower_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)16U, uint8_t *));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_slice_subslice3(bytes, (size_t)8U, (size_t)24U, uint8_t *));
  out[0U] =
      libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
          lower_coefficients, upper_coefficients);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_12(
    Eurydice_slice bytes, __m256i *out) {
  libcrux_ml_kem_vector_avx2_serialize_deserialize_12(bytes, out);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_deserialize_12_f5(
    Eurydice_slice input, __m256i *out) {
  libcrux_ml_kem_vector_avx2_deserialize_12(input, out);
}

static const uint8_t
    libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE
        [256U][16U] = {{255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {6U, 7U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 255U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {6U, 7U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 255U,
                        255U, 255U, 255U},
                       {12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {6U, 7U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 255U,
                        255U, 255U, 255U},
                       {10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U,
                        13U, 255U, 255U},
                       {14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {6U, 7U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 14U, 15U, 255U,
                        255U, 255U, 255U},
                       {10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 14U,
                        15U, 255U, 255U},
                       {12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U, 255U, 255U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {4U, 5U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 10U, 11U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U, 255U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {2U, 3U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 8U, 9U, 10U, 11U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U, 255U,
                        255U, 255U, 255U, 255U, 255U},
                       {0U, 1U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U, 15U,
                        255U, 255U, 255U, 255U},
                       {0U, 1U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U, 13U, 14U,
                        15U, 255U, 255U},
                       {0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U, 10U, 11U, 12U,
                        13U, 14U, 15U}};

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t
libcrux_ml_kem_vector_avx2_sampling_rejection_sample(Eurydice_slice input,
                                                     Eurydice_slice output) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi16(
      LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i potential_coefficients =
      libcrux_intrinsics_avx2_mm256_setzero_si256();
  libcrux_ml_kem_vector_avx2_serialize_deserialize_12(input,
                                                      &potential_coefficients);
  __m256i compare_with_field_modulus =
      libcrux_intrinsics_avx2_mm256_cmpgt_epi16(field_modulus,
                                                potential_coefficients);
  uint8_t good[2U] = {0U};
  libcrux_ml_kem_vector_avx2_serialize_serialize_1(
      &compare_with_field_modulus,
      Eurydice_array_to_slice((size_t)2U, good, uint8_t));
  uint8_t lower_shuffles[16U];
  memcpy(lower_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[0U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i lower_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, lower_shuffles, uint8_t));
  __m128i lower_coefficients =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(potential_coefficients);
  __m128i lower_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      lower_coefficients, lower_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(output, lower_coefficients0);
  size_t sampled_count = (size_t)core_num__u8__count_ones(good[0U]);
  uint8_t upper_shuffles[16U];
  memcpy(upper_shuffles,
         libcrux_ml_kem_vector_rej_sample_table_REJECTION_SAMPLE_SHUFFLE_TABLE[(
             size_t)good[1U]],
         (size_t)16U * sizeof(uint8_t));
  __m128i upper_shuffles0 = libcrux_intrinsics_avx2_mm_loadu_si128(
      Eurydice_array_to_slice((size_t)16U, upper_shuffles, uint8_t));
  __m128i upper_coefficients = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, potential_coefficients, __m128i);
  __m128i upper_coefficients0 = libcrux_intrinsics_avx2_mm_shuffle_epi8(
      upper_coefficients, upper_shuffles0);
  libcrux_intrinsics_avx2_mm_storeu_si128(
      Eurydice_slice_subslice3(output, sampled_count,
                               sampled_count + (size_t)8U, int16_t *),
      upper_coefficients0);
  size_t uu____0 = sampled_count;
  return uu____0 + (size_t)core_num__u8__count_ones(good[1U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE size_t libcrux_ml_kem_vector_avx2_rej_sample_f5(
    Eurydice_slice input, Eurydice_slice out) {
  return libcrux_ml_kem_vector_avx2_sampling_rejection_sample(input, out);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_avx2_SIMD256Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_f6_s {
  __m256i coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_f6;

/**
A monomorphic instance of
libcrux_ml_kem.polynomial.{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]}.ZERO.{core::ops::function::FnMut<(usize),␣Vector>␣for␣libcrux_ml_kem::polynomial::{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]}::ZERO::closure<Vector>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i
libcrux_ml_kem_polynomial__libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___ZERO__core__ops__function__FnMut__usize___Vector__for_libcrux_ml_kem__polynomial___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1____ZERO__closure_Vector__TraitClause_0__TraitClause_1___call_mut_06(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_vector_avx2_ZERO_f5();
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_polynomial_ZERO_d6_06(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 lit;
  __m256i ret[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_polynomial__libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___ZERO__core__ops__function__FnMut__usize___Vector__for_libcrux_ml_kem__polynomial___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1____ZERO__closure_Vector__TraitClause_0__TraitClause_1___call_mut_06(
            &lvalue, i);
  }
  memcpy(lit.coefficients, ret, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_decrypt_call_mut_0b_2f(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_06(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_avx2_deserialize_12_f5(bytes, &re->coefficients[i0]);
  }
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_deserialize_vector_ab(
    Eurydice_slice secret_key, Eurydice_slice secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_deserialize_to_uncompressed_ring_element_06(
        Eurydice_slice_subslice3(
            secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *),
        &Eurydice_slice_index(
            secret_as_ntt, i0,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
  }
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector,
K, CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked.call_mut_68
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_decrypt_unpacked_call_mut_68_2f(void **_,
                                                       size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_ef(
    __m256i *vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)10);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)10, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)10, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  vector[0U] = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, __m256i);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_f5_ef(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_ef(vec);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_10_06(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    libcrux_ml_kem_vector_avx2_deserialize_10_f5(bytes, &re->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_f5_ef(
        &re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_ee(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *output) {
  libcrux_ml_kem_serialize_deserialize_then_decompress_10_06(serialized,
                                                             output);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.montgomery_multiply_fe
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_traits_montgomery_multiply_fe_06(__m256i *v,
                                                       int16_t fer) {
  libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(v, fer);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_layer_int_vec_step_06(
    __m256i *coefficients, size_t a, size_t b, __m256i *scratch,
    int16_t zeta_r) {
  scratch[0U] = coefficients[b];
  libcrux_ml_kem_vector_traits_montgomery_multiply_fe_06(scratch, zeta_r);
  coefficients[b] = coefficients[a];
  libcrux_ml_kem_vector_avx2_add_f5(&coefficients[a], scratch);
  libcrux_ml_kem_vector_avx2_sub_f5(&coefficients[b], scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    size_t layer, __m256i *scratch, size_t _initial_coefficient_bound) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec = step / (size_t)16U;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_ntt_ntt_layer_int_vec_step_06(
          re->coefficients, a_offset + j, b_offset + j, scratch,
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_3_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_avx2_ntt_layer_3_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_2_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_avx2_ntt_layer_2_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_1_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    size_t _initial_coefficient_bound) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    libcrux_ml_kem_vector_avx2_ntt_layer_1_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)2U),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)3U));
    zeta_i[0U] = zeta_i[0U] + (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&myself->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self) {
  libcrux_ml_kem_polynomial_poly_barrett_reduce_06(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_vector_u_ee(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, __m256i *scratch) {
  size_t zeta_i = (size_t)0U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)7U, scratch,
                                            (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)6U, scratch,
                                            (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)5U, scratch,
                                            (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)4U, scratch,
                                            (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_06(&zeta_i, re, (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_06(&zeta_i, re, (size_t)6U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_06(&zeta_i, re, (size_t)7U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_06(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_ed(uint8_t *ciphertext,
                                                        Eurydice_slice u_as_ntt,
                                                        __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_u_ee(
        u_bytes,
        &Eurydice_slice_index(
            u_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
    libcrux_ml_kem_ntt_ntt_vector_u_ee(
        &Eurydice_slice_index(
            u_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
        scratch);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.decompress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_d1(
    __m256i *vector) {
  __m256i field_modulus = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  __m256i two_pow_coefficient_bits = libcrux_intrinsics_avx2_mm256_set1_epi32(
      (int32_t)1 << (uint32_t)(int32_t)4);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i decompressed_low = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_low0, field_modulus);
  __m256i decompressed_low0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_low, __m256i);
  __m256i decompressed_low1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_low0, two_pow_coefficient_bits);
  __m256i decompressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)4, decompressed_low1, __m256i);
  __m256i decompressed_low3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_low2, __m256i);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i decompressed_high = libcrux_intrinsics_avx2_mm256_mullo_epi32(
      coefficients_high0, field_modulus);
  __m256i decompressed_high0 = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)1, decompressed_high, __m256i);
  __m256i decompressed_high1 = libcrux_intrinsics_avx2_mm256_add_epi32(
      decompressed_high0, two_pow_coefficient_bits);
  __m256i decompressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)4, decompressed_high1, __m256i);
  __m256i decompressed_high3 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)1, decompressed_high2, __m256i);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      decompressed_low3, decompressed_high3);
  vector[0U] = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, __m256i);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.decompress_ciphertext_coefficient_f5 with const
generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_f5_d1(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_compress_decompress_ciphertext_coefficient_d1(vec);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_4_06(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    libcrux_ml_kem_vector_avx2_deserialize_4_f5(bytes, &re->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_decompress_ciphertext_coefficient_f5_d1(
        &re->coefficients[i0]);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_ed(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *output) {
  libcrux_ml_kem_serialize_deserialize_then_decompress_4_06(serialized, output);
}

/**
 Given two `KyberPolynomialRingElement`s in their NTT representations,
 compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
 the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:

 ```plaintext
 ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X²
 - ζ^(2·BitRev₇(i) + 1))
 ```

 This function almost implements <strong>Algorithm 10</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
 Output: An array ĥ ∈ ℤq.

 for(i ← 0; i < 128; i++)
     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1],
 ζ^(2·BitRev₇(i) + 1)) end for return ĥ
 ```
 We say "almost" because the coefficients of the ring element output by
 this function are in the Montgomery domain.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_ntt_multiply_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *out) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_ntt_multiply_f5(
        &myself->coefficients[i0], &rhs->coefficients[i0],
        &out->coefficients[i0],
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)1U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)2U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_ntt_multiply_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *out) {
  libcrux_ml_kem_polynomial_ntt_multiply_06(self, rhs, out);
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)16U, myself->coefficients, __m256i),
                              __m256i);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_add_f5(&myself->coefficients[i0],
                                      &rhs->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_to_ring_element_d6_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *rhs) {
  libcrux_ml_kem_polynomial_add_to_ring_element_ab(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)2U),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)3U));
    zeta_i[0U] = zeta_i[0U] - (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
        libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_f5(
        &re->coefficients[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_06(
    __m256i *coefficients, size_t a, size_t b,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch,
    int16_t zeta_r) {
  scratch->coefficients[0U] = coefficients[a];
  scratch->coefficients[1U] = coefficients[b];
  libcrux_ml_kem_vector_avx2_add_f5(&coefficients[a],
                                    &scratch->coefficients[1U]);
  libcrux_ml_kem_vector_avx2_sub_f5(&coefficients[b], scratch->coefficients);
  libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&coefficients[a]);
  libcrux_ml_kem_vector_traits_montgomery_multiply_fe_06(&coefficients[b],
                                                         zeta_r);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_06(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    size_t layer, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec =
      step / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_invert_ntt_inv_ntt_layer_int_vec_step_reduce_06(
          re->coefficients, a_offset + j, b_offset + j, scratch,
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_1_06(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_2_06(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_3_06(&zeta_i, re);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_06(&zeta_i, re,
                                                          (size_t)4U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_06(&zeta_i, re,
                                                          (size_t)5U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_06(&zeta_i, re,
                                                          (size_t)6U, scratch);
  libcrux_ml_kem_invert_ntt_invert_ntt_at_layer_4_plus_06(&zeta_i, re,
                                                          (size_t)7U, scratch);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_06(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_subtract_reduce_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
        &b->coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_avx2_sub_f5(&b->coefficients[i0],
                                      &myself->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_negate_f5(&b->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&b->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_subtract_reduce_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *b) {
  libcrux_ml_kem_polynomial_subtract_reduce_06(self, b);
}

/**
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_message_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *u_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_ntt_multiply_d6_06(&secret_as_ntt[i0],
                                                 &u_as_ntt[i0], scratch);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_ab(result, scratch);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_ab(result, scratch);
  libcrux_ml_kem_polynomial_subtract_reduce_d6_06(v, result);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_to_unsigned_field_modulus_06(__m256i *a,
                                                      __m256i *out) {
  __m256i uu____0 =
      libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(a[0U]);
  out[0U] = uu____0;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_message_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    Eurydice_slice serialized, __m256i *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_06(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_avx2_compress_1_f5(scratch);
    libcrux_ml_kem_vector_avx2_serialize_1_f5(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)2U * i0,
                                 (size_t)2U * i0 + (size_t)2U, uint8_t *));
  }
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_decrypt_unpacked_2f(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63 *secret_key,
    uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    u_as_ntt[i] =
        libcrux_ml_kem_ind_cpa_decrypt_unpacked_call_mut_68_2f(&lvalue, i);
  }
  libcrux_ml_kem_ind_cpa_deserialize_then_decompress_u_ed(
      ciphertext,
      Eurydice_array_to_slice(
          (size_t)3U, u_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_serialize_deserialize_then_decompress_ring_element_v_ed(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]),
      &v);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_matrix_compute_message_ab(&v, secret_key->secret_as_ntt,
                                           u_as_ntt, &message, scratch);
  libcrux_ml_kem_serialize_compress_then_serialize_message_06(
      &message, decrypted, scratch->coefficients);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_decrypt_2f(
    Eurydice_slice secret_key, uint8_t *ciphertext, Eurydice_slice decrypted,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] = libcrux_ml_kem_ind_cpa_decrypt_call_mut_0b_2f(&lvalue, i);
  }
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_ind_cpa_deserialize_vector_ab(
      secret_key, Eurydice_array_to_slice(
                      (size_t)3U, secret_key_unpacked.secret_as_ntt,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_2f(&secret_key_unpacked, ciphertext,
                                             decrypted, scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 32
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_9e(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_26
with const generics
- LEN= 32
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_26_9e(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_avx2_PRF_9e(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate.call_mut_5f
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_decapsulate_call_mut_5f_57(void **_,
                                                  size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
- $9size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[9U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}::default::closure<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_ed(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}::default::closure#1<Vector,␣K,␣K_SQUARED>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_1_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_ed(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_50
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0
libcrux_ml_kem_ind_cpa_unpacked_default_50_ed(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    uu____0[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_ed(
            &lvalue, i);
  }
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPublicKeyUnpacked_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1____default__closure_1_Vector__K__K_SQUARED__TraitClause_0__TraitClause_1___call_mut_ed(
            &lvalue, i);
  }
  memcpy(
      lit.A, ret,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
 Only use with public values.

 This MUST NOT be used with secret inputs, like its caller
 `deserialize_ring_elements_reduced`.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_06(
    Eurydice_slice serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_avx2_deserialize_12_f5(bytes, &re->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_cond_subtract_3329_f5(&re->coefficients[i0]);
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_ab(
    Eurydice_slice public_key, Eurydice_slice deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    libcrux_ml_kem_serialize_deserialize_to_reduced_ring_element_06(
        ring_element,
        &Eurydice_slice_index(
            deserialized_pk, i0,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
  }
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 504
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i1, uint8_t[504U], uint8_t(*)[504U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i1;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- N= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed0(
    Eurydice_slice randomness, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *) <
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        uint8_t *randomness_i = Eurydice_slice_index(
            randomness, i1, uint8_t[168U], uint8_t(*)[168U]);
        int16_t *out_i =
            Eurydice_slice_index(out, i1, int16_t[272U], int16_t(*)[272U]);
        size_t sampled_coefficients_i =
            Eurydice_slice_index(sampled_coefficients, i1, size_t, size_t *);
        size_t sampled = libcrux_ml_kem_vector_avx2_rej_sample_f5(
            Eurydice_array_to_subslice3(randomness_i, r * (size_t)24U,
                                        r * (size_t)24U + (size_t)24U,
                                        uint8_t *),
            Eurydice_array_to_subslice3(out_i, sampled_coefficients_i,
                                        sampled_coefficients_i + (size_t)16U,
                                        int16_t *));
        size_t uu____0 = i1;
        Eurydice_slice_index(sampled_coefficients, uu____0, size_t, size_t *) =
            Eurydice_slice_index(sampled_coefficients, uu____0, size_t,
                                 size_t *) +
            sampled;
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) >=
        LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      Eurydice_slice_index(sampled_coefficients, i0, size_t, size_t *) =
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_6c(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_55 xof_state =
      libcrux_ml_kem_hash_functions_avx2_shake128_init_absorb_final_26(seeds);
  uint8_t randomness[3U][504U] = {{0U}};
  uint8_t randomness_blocksize[3U][168U] = {{0U}};
  libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_first_three_blocks_26(
      &xof_state,
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]));
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed(
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_ml_kem_hash_functions_avx2_shake128_squeeze_next_block_26(
          &xof_state, Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                              uint8_t[168U]));
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed0(
          Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_from_i16_array_06(
    Eurydice_slice a,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_from_i16_array_f5(
        Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                 (i0 + (size_t)1U) * (size_t)16U, int16_t *),
        &result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_from_i16_array_d6_06(
    Eurydice_slice a, libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *out) {
  libcrux_ml_kem_polynomial_from_i16_array_06(a, out);
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_6c(
    Eurydice_slice A_transpose, uint8_t *seed, bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_seed[34U];
    memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
    uint8_t seeds[3U][34U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t));
    }
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds[j][32U] = (uint8_t)i1;
      seeds[j][33U] = (uint8_t)j;
    }
    size_t sampled_coefficients[3U] = {0U};
    int16_t out[3U][272U] = {{0U}};
    libcrux_ml_kem_sampling_sample_from_xof_6c(
        Eurydice_array_to_slice((size_t)3U, seeds, uint8_t[34U]),
        Eurydice_array_to_slice((size_t)3U, sampled_coefficients, size_t),
        Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]));
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]),
                 int16_t[272U]);
         i++) {
      size_t j = i;
      int16_t sample[272U];
      memcpy(sample, out[j], (size_t)272U * sizeof(int16_t));
      if (transpose) {
        Eurydice_slice uu____1 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_06(
            uu____1, &Eurydice_slice_index(
                         A_transpose, j * (size_t)3U + i1,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
      } else {
        Eurydice_slice uu____2 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_06(
            uu____2, &Eurydice_slice_index(
                         A_transpose, i1 * (size_t)3U + j,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
      }
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_b4(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_ab(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, unpacked_public_key->t_as_ntt,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, unpacked_public_key->A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_6c(uu____1, ret, false);
}

/**
 Given a series of uniformly random bytes in `randomness`, for some number
 `eta`, the `sample_from_binomial_distribution_{eta}` functions sample a ring
 element from a binomial distribution centered at 0 that uses two sets of `eta`
 coin flips. If, for example, `eta = ETA`, each ring coefficient is a value `v`
 such such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:

 ```plaintext
 - If v < 0, Pr[v] = Pr[-v]
 - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
 ```

 The values `v < 0` are mapped to the appropriate `KyberFieldElement`.

 The expected value is:

 ```plaintext
 E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1]
 + (ETA)Pr[ETA] = 0 since Pr[-v] = Pr[v] when v < 0.
 ```

 And the variance is:

 ```plaintext
 Var(X) = E[(X - E[X])^2]
        = E[X^2]
        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) /
 2^(2 * ETA)) = ETA / 2
 ```

 This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203
 standard, which is reproduced below:

 ```plaintext
 Input: byte array B ∈ 𝔹^{64η}.
 Output: array f ∈ ℤ₂₅₆.

 b ← BytesToBits(B)
 for (i ← 0; i < 256; i++)
     x ← ∑(j=0 to η - 1) b[2iη + j]
     y ← ∑(j=0 to η - 1) b[2iη + η + j]
     f[i] ← x−y mod q
 end for
 return f
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_06(
    Eurydice_slice randomness, Eurydice_slice sampled_i16s) {
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t *);
    uint32_t random_bits_as_u32 =
        (((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                         uint8_t *) |
          (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                         uint8_t *)
              << 8U) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                        uint8_t *)
             << 16U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U, uint8_t,
                                       uint8_t *)
            << 24U;
    uint32_t even_bits = random_bits_as_u32 & 1431655765U;
    uint32_t odd_bits = random_bits_as_u32 >> 1U & 1431655765U;
    uint32_t coin_toss_outcomes = even_bits + odd_bits;
    for (uint32_t i = 0U; i < 32U / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      Eurydice_slice_index(sampled_i16s, (size_t)8U * chunk_number + offset,
                           int16_t, int16_t *) = outcome_1 - outcome_2;
    }
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- ETA= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_sampling_sample_from_binomial_distribution_89(
    Eurydice_slice randomness, int16_t *output) {
  libcrux_ml_kem_sampling_sample_from_binomial_distribution_2_06(
      randomness, Eurydice_array_to_slice((size_t)256U, output, int16_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ntt_ntt_at_layer_7_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, __m256i *scratch) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    scratch[0U] = re->coefficients[j + step];
    libcrux_ml_kem_vector_avx2_multiply_by_constant_f5(scratch, (int16_t)-1600);
    re->coefficients[j + step] = re->coefficients[j];
    libcrux_ml_kem_vector_avx2_add_f5(&re->coefficients[j], scratch);
    libcrux_ml_kem_vector_avx2_sub_f5(&re->coefficients[j + step], scratch);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, __m256i *scratch) {
  libcrux_ml_kem_ntt_ntt_at_layer_7_06(re, scratch);
  size_t zeta_i = (size_t)1U;
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)6U, scratch,
                                            (size_t)11207U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(&zeta_i, re, (size_t)5U, scratch,
                                            (size_t)11207U + (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_4_plus_06(
      &zeta_i, re, (size_t)4U, scratch,
      (size_t)11207U + (size_t)2U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_3_06(
      &zeta_i, re, (size_t)11207U + (size_t)3U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_2_06(
      &zeta_i, re, (size_t)11207U + (size_t)4U * (size_t)3328U);
  libcrux_ml_kem_ntt_ntt_at_layer_1_06(
      &zeta_i, re, (size_t)11207U + (size_t)5U * (size_t)3328U);
  libcrux_ml_kem_polynomial_poly_barrett_reduce_d6_06(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_cb(Eurydice_slice re_as_ntt,
                                                     uint8_t *prf_input,
                                                     uint8_t domain_separator,
                                                     __m256i *scratch) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_PRFxN_26(
      Eurydice_array_to_slice((size_t)3U, prf_inputs, uint8_t[33U]),
      Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_slice randomness = Eurydice_array_to_subslice3(
        prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
        uint8_t *);
    int16_t sample_buffer[256U] = {0U};
    libcrux_ml_kem_sampling_sample_from_binomial_distribution_89(randomness,
                                                                 sample_buffer);
    libcrux_ml_kem_polynomial_from_i16_array_d6_06(
        Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
        &Eurydice_slice_index(
            re_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
    libcrux_ml_kem_ntt_ntt_binomially_sampled_ring_element_06(
        &Eurydice_slice_index(
            re_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
        scratch);
  }
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_77
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_77_a1(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE uint8_t
libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_cb(uint8_t *prf_input,
                                                  uint8_t domain_separator,
                                                  Eurydice_slice error_1,
                                                  int16_t *sample_buffer) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_prf_input[33U];
  memcpy(copy_of_prf_input, prf_input, (size_t)33U * sizeof(uint8_t));
  uint8_t prf_inputs[3U][33U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    memcpy(prf_inputs[i], copy_of_prf_input, (size_t)33U * sizeof(uint8_t));
  }
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[384U] = {0U};
  Eurydice_slice uu____1 = core_array___Array_T__N___as_slice(
      (size_t)3U, prf_inputs, uint8_t[33U], Eurydice_slice);
  libcrux_ml_kem_hash_functions_avx2_PRFxN_26(
      uu____1, Eurydice_array_to_slice((size_t)384U, prf_outputs, uint8_t),
      (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_slice randomness = Eurydice_array_to_subslice3(
        prf_outputs, i0 * (size_t)128U, (i0 + (size_t)1U) * (size_t)128U,
        uint8_t *);
    libcrux_ml_kem_sampling_sample_from_binomial_distribution_89(randomness,
                                                                 sample_buffer);
    libcrux_ml_kem_polynomial_from_i16_array_d6_06(
        Eurydice_array_to_slice((size_t)256U, sample_buffer, int16_t),
        &Eurydice_slice_index(
            error_1, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF
with const generics
- LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_a6(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_sha3_portable_shake256(out, input);
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash for
libcrux_ml_kem::hash_functions::avx2::Simd256Hash}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.avx2.PRF_26
with const generics
- LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_avx2_PRF_26_a6(
    Eurydice_slice input, Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_avx2_PRF_a6(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_88
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_88_a1(void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.entry
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *
libcrux_ml_kem_matrix_entry_ab(Eurydice_slice matrix, size_t i, size_t j) {
  return &Eurydice_slice_index(
      matrix, i * (size_t)3U + j,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
        &myself->coefficients[j], (int16_t)1441);
    libcrux_ml_kem_vector_avx2_add_f5(&myself->coefficients[j],
                                      &error->coefficients[j]);
    libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_add_error_reduce_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  libcrux_ml_kem_polynomial_add_error_reduce_06(self, error);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_vector_u_ab(
    Eurydice_slice a_as_ntt, Eurydice_slice r_as_ntt, Eurydice_slice error_1,
    Eurydice_slice result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____0 =
          libcrux_ml_kem_matrix_entry_ab(a_as_ntt, i1, j);
      libcrux_ml_kem_polynomial_ntt_multiply_d6_06(
          uu____0,
          &Eurydice_slice_index(
              r_as_ntt, j, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
              libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
          scratch);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_ab(
          &Eurydice_slice_index(
              result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
              libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
          scratch);
    }
    libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_ab(
        &Eurydice_slice_index(
            result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
        scratch);
    libcrux_ml_kem_polynomial_add_error_reduce_d6_06(
        &Eurydice_slice_index(
            result, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
        &Eurydice_slice_index(
            error_1, i1, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_ef(
    __m256i *vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)10) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)10, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)10, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  vector[0U] = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, __m256i);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_ef(
    __m256i *vector) {
  libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_ef(
      vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 10
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_f5_ef(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_compress_ef(vec);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- OUT_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_10_0e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    Eurydice_slice serialized, __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_06(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_avx2_compress_f5_ef(scratch);
    libcrux_ml_kem_vector_avx2_serialize_10_f5(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)20U * i0,
                                 (size_t)20U * i0 + (size_t)20U, uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_a4(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re,
    Eurydice_slice serialized, __m256i *scratch) {
  libcrux_ml_kem_serialize_compress_then_serialize_10_0e(re, serialized,
                                                         scratch);
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_compress_then_serialize_u_8c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 input[3U],
    Eurydice_slice out, __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = input[i0];
    libcrux_ml_kem_serialize_compress_then_serialize_ring_element_u_a4(
        &re,
        Eurydice_slice_subslice3(
            out, i0 * ((size_t)960U / (size_t)3U),
            (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_c1_a1(
    Eurydice_slice randomness,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *matrix,
    Eurydice_slice ciphertext, Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  uint8_t domain_separator0 =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_cb(
          r_as_ntt, prf_input, 0U, scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_1[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    error_1[i] = libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_77_a1(&lvalue, i);
  }
  int16_t sampling_buffer[256U] = {0U};
  uint8_t domain_separator = libcrux_ml_kem_ind_cpa_sample_ring_element_cbd_cb(
      prf_input, domain_separator0,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      sampling_buffer);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_PRF_26_a6(
      Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_sampling_sample_from_binomial_distribution_89(
      Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t),
      sampling_buffer);
  libcrux_ml_kem_polynomial_from_i16_array_d6_06(
      Eurydice_array_to_slice((size_t)256U, sampling_buffer, int16_t), error_2);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 u[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    u[i] = libcrux_ml_kem_ind_cpa_encrypt_c1_call_mut_88_a1(&lvalue, i);
  }
  libcrux_ml_kem_matrix_compute_vector_u_ab(
      Eurydice_array_to_slice(
          (size_t)9U, matrix,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      r_as_ntt,
      Eurydice_array_to_slice(
          (size_t)3U, error_1,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      Eurydice_array_to_slice(
          (size_t)3U, u, libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      scratch);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 copy_of_u[3U];
  memcpy(
      copy_of_u, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_ind_cpa_compress_then_serialize_u_8c(copy_of_u, ciphertext,
                                                      scratch->coefficients);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.traits.decompress_1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_traits_decompress_1_06(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_negate_f5(vec);
  libcrux_ml_kem_vector_avx2_bitwise_and_with_constant_f5(vec, (int16_t)1665);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_deserialize_then_decompress_message_06(
    uint8_t *serialized,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_deserialize_1_f5(
        Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                    (size_t)2U * i0 + (size_t)2U, uint8_t *),
        &re->coefficients[i0]);
    libcrux_ml_kem_vector_traits_decompress_1_06(&re->coefficients[i0]);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_message_error_reduce_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *result,
    __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
        &result->coefficients[i0], (int16_t)1441);
    scratch[0U] = myself->coefficients[i0];
    libcrux_ml_kem_vector_avx2_add_f5(scratch, &message->coefficients[i0]);
    libcrux_ml_kem_vector_avx2_add_f5(&result->coefficients[i0], scratch);
    libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&result->coefficients[i0]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_message_error_reduce_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *result,
    __m256i *scratch) {
  libcrux_ml_kem_polynomial_add_message_error_reduce_06(self, message, result,
                                                        scratch);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_ring_element_v_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *result,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_ntt_multiply_d6_06(
        &t_as_ntt[i0],
        &Eurydice_slice_index(
            r_as_ntt, i0, libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
            libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *),
        scratch);
    libcrux_ml_kem_polynomial_add_to_ring_element_d6_ab(result, scratch);
  }
  libcrux_ml_kem_invert_ntt_invert_ntt_montgomery_ab(result, scratch);
  libcrux_ml_kem_polynomial_add_message_error_reduce_d6_06(
      error_2, message, result, scratch->coefficients);
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.avx2.compress.compress_ciphertext_coefficient with const
generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_d1(
    __m256i *vector) {
  __m256i field_modulus_halved = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS - (int32_t)1) /
      (int32_t)2);
  __m256i compression_factor =
      libcrux_intrinsics_avx2_mm256_set1_epi32((int32_t)10321340);
  __m256i coefficient_bits_mask = libcrux_intrinsics_avx2_mm256_set1_epi32(
      ((int32_t)1 << (uint32_t)(int32_t)4) - (int32_t)1);
  __m128i coefficients_low =
      libcrux_intrinsics_avx2_mm256_castsi256_si128(vector[0U]);
  __m256i coefficients_low0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_low);
  __m256i compressed_low = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)4, coefficients_low0, __m256i);
  __m256i compressed_low0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_low, field_modulus_halved);
  __m256i compressed_low1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_low0,
                                                            compression_factor);
  __m256i compressed_low2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_low1, __m256i);
  __m256i compressed_low3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_low2, coefficient_bits_mask);
  __m128i coefficients_high = libcrux_intrinsics_avx2_mm256_extracti128_si256(
      (int32_t)1, vector[0U], __m128i);
  __m256i coefficients_high0 =
      libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(coefficients_high);
  __m256i compressed_high = libcrux_intrinsics_avx2_mm256_slli_epi32(
      (int32_t)4, coefficients_high0, __m256i);
  __m256i compressed_high0 = libcrux_intrinsics_avx2_mm256_add_epi32(
      compressed_high, field_modulus_halved);
  __m256i compressed_high1 =
      libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(compressed_high0,
                                                            compression_factor);
  __m256i compressed_high2 = libcrux_intrinsics_avx2_mm256_srli_epi32(
      (int32_t)3, compressed_high1, __m256i);
  __m256i compressed_high3 = libcrux_intrinsics_avx2_mm256_and_si256(
      compressed_high2, coefficient_bits_mask);
  __m256i compressed = libcrux_intrinsics_avx2_mm256_packs_epi32(
      compressed_low3, compressed_high3);
  vector[0U] = libcrux_intrinsics_avx2_mm256_permute4x64_epi64(
      (int32_t)216, compressed, __m256i);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress
with const generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_d1(
    __m256i *vector) {
  libcrux_ml_kem_vector_avx2_compress_compress_ciphertext_coefficient_d1(
      vector);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.avx2.compress_f5
with const generics
- COEFFICIENT_BITS= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_vector_avx2_compress_f5_d1(
    __m256i *vec) {
  libcrux_ml_kem_vector_avx2_compress_d1(vec);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_4_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re,
    Eurydice_slice serialized, __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_06(&re.coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_avx2_compress_f5_d1(scratch);
    libcrux_ml_kem_vector_avx2_serialize_4_f5(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *));
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re, Eurydice_slice out,
    __m256i *scratch) {
  libcrux_ml_kem_serialize_compress_then_serialize_4_06(re, out, scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_c2_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    uint8_t *message, Eurydice_slice ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 message_as_ring_element =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_serialize_deserialize_then_decompress_message_06(
      message, &message_as_ring_element);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 v =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_matrix_compute_ring_element_v_ab(
      t_as_ntt, r_as_ntt, error_2, &message_as_ring_element, &v, scratch);
  libcrux_ml_kem_serialize_compress_then_serialize_ring_element_v_ed(
      v, ciphertext, scratch->coefficients);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_unpacked_67(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 *public_key,
    uint8_t *message, Eurydice_slice randomness, Eurydice_slice ciphertext,
    Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_ind_cpa_encrypt_c1_a1(
      randomness, public_key->A,
      Eurydice_slice_subslice3(ciphertext, (size_t)0U, (size_t)960U, uint8_t *),
      r_as_ntt, error_2, scratch);
  libcrux_ml_kem_ind_cpa_encrypt_c2_ed(
      public_key->t_as_ntt, r_as_ntt, error_2, message,
      Eurydice_slice_subslice_from(ciphertext, (size_t)960U, uint8_t, size_t,
                                   uint8_t[]),
      scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_encrypt_67(
    Eurydice_slice public_key, uint8_t *message, Eurydice_slice randomness,
    Eurydice_slice ciphertext, Eurydice_slice r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0
      unpacked_public_key = libcrux_ml_kem_ind_cpa_unpacked_default_50_ed();
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_b4(public_key,
                                                          &unpacked_public_key);
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_67(&unpacked_public_key, message,
                                             randomness, ciphertext, r_as_ntt,
                                             error_2, scratch);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_kdf_39_ae(
    Eurydice_slice shared_secret, uint8_t *_, Eurydice_slice out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_decapsulate_57(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_decrypt_2f(
      ind_cpa_secret_key, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_G_26(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_PRF_26_9e(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t));
  uint8_t expected_ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] = libcrux_ml_kem_ind_cca_decapsulate_call_mut_5f_57(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_encrypt_67(
      ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      &error_2, &scratch);
  uint8_t implicit_rejection_shared_secret_kdf[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_ae(
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t));
  uint8_t shared_secret_kdf[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_ae(
      shared_secret0, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t));
  uint8_t shared_secret[32U] = {0U};
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret_kdf, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret_kdf,
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t));
  memcpy(ret, shared_secret, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate_avx2 with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_avx2_54(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_57(private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_54(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_avx2_54(
      private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_54(private_key,
                                                            ciphertext, ret);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_entropy_preprocess_39_3f(
    Eurydice_slice randomness, Eurydice_slice out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate.call_mut_c0
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_encapsulate_call_mut_c0_a1(void **_,
                                                  size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_encapsulate_a1(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  uint8_t processed_randomness[32U] = {0U};
  libcrux_ml_kem_variant_entropy_preprocess_39_3f(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t));
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, processed_randomness, uint8_t),
      to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t);
  libcrux_ml_kem_hash_functions_avx2_H_26(
      uu____0, Eurydice_array_to_subslice_from(
                   (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                   uint8_t, size_t, uint8_t[]));
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_G_26(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext ciphertext =
      libcrux_ml_kem_types_default_73_80();
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] = libcrux_ml_kem_ind_cca_encapsulate_call_mut_c0_a1(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_encrypt_67(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_e6_d0(public_key),
                              uint8_t),
      processed_randomness, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, ciphertext.value, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      &error_2, &scratch);
  uint8_t shared_secret_array[32U] = {0U};
  libcrux_ml_kem_variant_kdf_39_ae(
      shared_secret, ciphertext.value,
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 = ciphertext;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate_avx2 with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_avx2_35(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_a1(public_key, randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate
with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_35(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_avx2_35(
      public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2 libcrux_ml_kem_mlkem768_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t randomness[32U]) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_35(public_key,
                                                                   randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,␣K>[TraitClause@0,␣TraitClause@1]}.default.{core::ops::function::FnMut<(usize),␣libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,␣TraitClause@1]>␣for␣libcrux_ml_kem::ind_cpa::unpacked::{core::default::Default␣for␣libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,␣K>[TraitClause@0,␣TraitClause@1]}::default::closure<Vector,␣K>[TraitClause@0,␣TraitClause@1]}.call_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1____default__closure_Vector__K__TraitClause_0__TraitClause_1___call_mut_ab(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63
libcrux_ml_kem_ind_cpa_unpacked_default_70_ab(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    ret[i] =
        libcrux_ml_kem_ind_cpa_unpacked__core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1___default__core__ops__function__FnMut__usize___libcrux_ml_kem__polynomial__PolynomialRingElement_Vector__TraitClause_0__TraitClause_1___for_libcrux_ml_kem__ind_cpa__unpacked___core__default__Default_for_libcrux_ml_kem__ind_cpa__unpacked__IndCpaPrivateKeyUnpacked_Vector__K__TraitClause_0__TraitClause_1____default__closure_Vector__K__TraitClause_0__TraitClause_1___call_mut_ab(
            &lvalue, i);
  }
  memcpy(
      lit.secret_as_ntt, ret,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_variant_cpa_keygen_seed_39_3f(
    Eurydice_slice key_generation_seed, Eurydice_slice out) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  libcrux_ml_kem_hash_functions_avx2_G_26(
      Eurydice_array_to_slice((size_t)33U, seed, uint8_t), out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_ae with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_call_mut_ae_5d(
    void **_, size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_polynomial_to_standard_domain_06(
    __m256i *vector) {
  libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
      vector,
      LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_polynomial_to_standard_domain_06(&myself->coefficients[j]);
    libcrux_ml_kem_vector_avx2_add_f5(&myself->coefficients[j],
                                      &error->coefficients[j]);
    libcrux_ml_kem_vector_avx2_barrett_reduce_f5(&myself->coefficients[j]);
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_d6
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error) {
  libcrux_ml_kem_polynomial_add_standard_error_reduce_06(self, error);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_compute_As_plus_e_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice matrix_A,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *error_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
        libcrux_ml_kem_polynomial_ZERO_d6_06();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U; i1 < (size_t)3U; i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____1 =
          libcrux_ml_kem_matrix_entry_ab(matrix_A, i0, j);
      libcrux_ml_kem_polynomial_ntt_multiply_d6_06(uu____1, &s_as_ntt[j],
                                                   scratch);
      libcrux_ml_kem_polynomial_add_to_ring_element_d6_ab(&t_as_ntt[i0],
                                                          scratch);
    }
    libcrux_ml_kem_polynomial_add_standard_error_reduce_d6_06(
        &t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_5d(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 *public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_variant_cpa_keygen_seed_39_3f(
      key_generation_seed,
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, public_key->A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_6c(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_cb(
          Eurydice_array_to_slice(
              (size_t)3U, private_key->secret_as_ntt,
              libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
          prf_input, 0U, scratch->coefficients);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    error_as_ntt[i] =
        libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_call_mut_ae_5d(&lvalue,
                                                                        i);
  }
  libcrux_ml_kem_ind_cpa_sample_vector_cbd_then_ntt_cb(
      Eurydice_array_to_slice(
          (size_t)3U, error_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      prf_input, domain_separator, scratch->coefficients);
  libcrux_ml_kem_matrix_compute_As_plus_e_ab(
      public_key->t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)9U, public_key->A,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      private_key->secret_as_ntt, error_as_ntt, scratch);
  uint8_t uu____2[32U];
  Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           TryFromSliceError);
  unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *re, __m256i *scratch,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_serialize_to_unsigned_field_modulus_06(&re->coefficients[i0],
                                                          scratch);
    libcrux_ml_kem_vector_avx2_serialize_12_f5(
        scratch,
        Eurydice_slice_subslice3(serialized, (size_t)24U * i0,
                                 (size_t)24U * i0 + (size_t)24U, uint8_t *));
  }
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_vector_ab(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *key, Eurydice_slice out,
    __m256i *scratch) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
               libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 re = key[i0];
    libcrux_ml_kem_serialize_serialize_uncompressed_ring_element_06(
        &re, scratch,
        Eurydice_slice_subslice3(
            out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            uint8_t *));
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *t_as_ntt,
    Eurydice_slice seed_for_a, Eurydice_slice serialized, __m256i *scratch) {
  libcrux_ml_kem_ind_cpa_serialize_vector_ab(
      t_as_ntt,
      Eurydice_slice_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t *),
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from(
          serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_8c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63 *private_key,
    Eurydice_slice serialized_private_key, Eurydice_slice serialized_public_key,
    __m256i *scratch) {
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      serialized_public_key, scratch);
  libcrux_ml_kem_ind_cpa_serialize_vector_ab(private_key->secret_as_ntt,
                                             serialized_private_key, scratch);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cpa_generate_keypair_d6(
    Eurydice_slice key_generation_seed,
    Eurydice_slice serialized_ind_cpa_private_key,
    Eurydice_slice serialized_public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *scratch) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63 private_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_70_ab();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 public_key =
      libcrux_ml_kem_ind_cpa_unpacked_default_50_ed();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_5d(
      key_generation_seed, &private_key, &public_key, scratch);
  libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_8c(
      &public_key, &private_key, serialized_ind_cpa_private_key,
      serialized_public_key, scratch->coefficients);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_ae(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  libcrux_ml_kem_hash_functions_avx2_H_26(
      public_key,
      Eurydice_array_to_subslice3(
          serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
          uint8_t *));
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____6 = serialized;
  size_t uu____7 = pointer;
  size_t uu____8 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____6, uu____7,
          uu____8 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_13(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t ind_cpa_private_key[1152U] = {0U};
  uint8_t public_key[1184U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_generate_keypair_d6(
      ind_cpa_keypair_randomness,
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t), &scratch);
  uint8_t secret_key_serialized[2400U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_ae(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 private_key =
      libcrux_ml_kem_types_from_77_28(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_d9 uu____1 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_74(
      uu____1, libcrux_ml_kem_types_from_fd_d0(copy_of_public_key));
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair_avx2 with const
generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_avx2_06(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_13(randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_06(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_avx2_06(
      randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_avx2_generate_key_pair(uint8_t randomness[64U]) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_06(
      randomness);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_only_ae(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_H_26(
      Eurydice_array_to_subslice3(private_key->value, (size_t)384U * (size_t)3U,
                                  (size_t)768U * (size_t)3U + (size_t)32U,
                                  uint8_t *),
      Eurydice_array_to_slice((size_t)32U, t, uint8_t));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_private_key_12(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_ae(private_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key_avx2 with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_avx2_31(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_12(private_key,
                                                        ciphertext);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_31(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_avx2_31(
      private_key, ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem768_avx2_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_31(
      private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key_only with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_only_41(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_ae(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem768_avx2_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_only_41(
      private_key);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key.call_mut_00
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_validate_public_key_call_mut_00_ed(void **_,
                                                          size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE bool libcrux_ml_kem_ind_cca_validate_public_key_ed(
    uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 deserialized_pk[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    deserialized_pk[i] =
        libcrux_ml_kem_ind_cca_validate_public_key_call_mut_00_ed(&lvalue, i);
  }
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key,
      libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_ab(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, deserialized_pk,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  uint8_t public_key_serialized[1184U] = {0U};
  __m256i scratch = libcrux_ml_kem_vector_avx2_ZERO_f5();
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *uu____1 = deserialized_pk;
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1184U, public_key,
      libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
      uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
      uu____1, uu____2,
      Eurydice_array_to_slice((size_t)1184U, public_key_serialized, uint8_t),
      &scratch);
  return Eurydice_array_eq((size_t)1184U, public_key, public_key_serialized,
                           uint8_t);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key_avx2 with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_avx2_41(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_ed(public_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool
libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_41(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_avx2_41(
      public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem768_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_41(
      public_key->value);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_63
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- $3size_t
- $9size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0;

typedef struct libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 public_key;
} libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for
libcrux_ml_kem::ind_cca::unpacked::decapsulate::closure<Vector, Hasher, K,
K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE, PUBLIC_KEY_SIZE,
CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.decapsulate.call_mut_03 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_unpacked_decapsulate_call_mut_03_37(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_decapsulate_37(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_decrypt_unpacked_2f(
      &key_pair->private_key.ind_cpa_private_key, ciphertext->value,
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), &scratch);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_G_26(
      Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t),
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_PRF_26_9e(
      Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t));
  uint8_t expected_ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] =
        libcrux_ml_kem_ind_cca_unpacked_decapsulate_call_mut_03_37(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_67(
      &key_pair->public_key.ind_cpa_public_key, decrypted, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      &error_2, &scratch);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t));
  uint8_t shared_secret_array[32U] = {0U};
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector,
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t));
  memcpy(ret, shared_secret_array, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.decapsulate_avx2 with const
generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_avx2_54(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_37(key_pair, ciphertext, ret);
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.decapsulate with const
generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_54(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_avx2_54(
      key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_decapsulate(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_54(
      private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash
with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_3f(
    Eurydice_slice randomness, Eurydice_slice pk_hash, uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  uint8_t output[64U] = {0U};
  libcrux_ml_kem_hash_functions_avx2_G_26(
      Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t),
      Eurydice_array_to_slice((size_t)64U, output, uint8_t));
  memcpy(ret, output, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for
libcrux_ml_kem::ind_cca::unpacked::encapsulate::closure<Vector, Hasher, K,
K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE,
C2_SIZE, VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR,
VECTOR_U_BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.encapsulate.call_mut_f7 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_unpacked_encapsulate_call_mut_f7_12(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE tuple_c2 libcrux_ml_kem_ind_cca_unpacked_encapsulate_12(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  libcrux_ml_kem_ind_cca_unpacked_encaps_prepare_3f(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, public_key->public_key_hash,
                              uint8_t),
      hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  uint8_t ciphertext[1088U] = {0U};
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 r_as_ntt[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    r_as_ntt[i] =
        libcrux_ml_kem_ind_cca_unpacked_encapsulate_call_mut_f7_12(&lvalue, i);
  }
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 error_2 =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_encrypt_unpacked_67(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness,
      Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
      Eurydice_array_to_slice(
          (size_t)3U, r_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      &error_2, &scratch);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 =
      libcrux_ml_kem_types_from_e0_80(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.encapsulate_avx2 with const
generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_avx2_35(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *public_key,
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_12(public_key, randomness);
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.encapsulate with const
generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_35(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *public_key,
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_avx2_35(
      public_key, randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_c2 libcrux_ml_kem_mlkem768_avx2_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *public_key,
    uint8_t randomness[32U]) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_35(
      public_key, randomness);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_5a with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_ind_cca_unpacked_transpose_a_call_mut_5a_ed(void **_,
                                                           size_t tupled_args) {
  return libcrux_ml_kem_polynomial_ZERO_d6_06();
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_c1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics

*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_f6
libcrux_ml_kem_polynomial_clone_c1_06(
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 lit;
  __m256i ret[16U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)16U, self->coefficients, ret, __m256i, void *);
  memcpy(lit.coefficients, ret, (size_t)16U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_transpose_a_ed(
    Eurydice_slice ind_cpa_a,
    libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[9U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    A[i] =
        libcrux_ml_kem_ind_cca_unpacked_transpose_a_call_mut_5a_ed(&lvalue, i);
  }
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0 =
          libcrux_ml_kem_polynomial_clone_c1_06(
              libcrux_ml_kem_matrix_entry_ab(ind_cpa_a, j, i1));
      A[i1 * (size_t)3U + j] = uu____0;
    }
  }
  memcpy(
      ret, A,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_avx2_Simd256Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_13(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 scratch0 =
      libcrux_ml_kem_polynomial_ZERO_d6_06();
  libcrux_ml_kem_ind_cpa_generate_keypair_unpacked_5d(
      ind_cpa_keypair_randomness, &out->private_key.ind_cpa_private_key,
      &out->public_key.ind_cpa_public_key, &scratch0);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 A[9U];
  libcrux_ml_kem_ind_cca_unpacked_transpose_a_ed(
      Eurydice_array_to_slice(
          (size_t)9U, out->public_key.ind_cpa_public_key.A,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6),
      A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[9U];
  memcpy(
      uu____0, A,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(
      out->public_key.ind_cpa_public_key.A, uu____0,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  uint8_t pk_serialized[1184U] = {0U};
  __m256i scratch = libcrux_ml_kem_vector_avx2_ZERO_f5();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t), &scratch);
  libcrux_ml_kem_hash_functions_avx2_H_26(
      Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t),
      Eurydice_array_to_slice((size_t)32U, out->public_key.public_key_hash,
                              uint8_t));
  uint8_t uu____1[32U];
  Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], TryFromSliceError);
  unwrap_26_b3(dst, uu____1);
  memcpy(out->private_key.implicit_rejection_value, uu____1,
         (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.generate_keypair_avx2 with
const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_avx2_06(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_13(copy_of_randomness, out);
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.generate_keypair with const
generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_06(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_avx2_06(
      copy_of_randomness, out);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_generate_key_pair_mut(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_06(
      copy_of_randomness, key_pair);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_3f
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
libcrux_ml_kem_ind_cca_unpacked_default_3f_ed(void) {
  return (libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0{
      libcrux_ml_kem_ind_cpa_unpacked_default_50_ed(), {0U}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_b1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
    libcrux_ml_kem_ind_cca_unpacked_default_b1_ed(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_63 uu____0 = {
      libcrux_ml_kem_ind_cpa_unpacked_default_70_ab(), {0U}};
  return (libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked{
      uu____0, libcrux_ml_kem_ind_cca_unpacked_default_3f_ed()});
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_avx2_unpacked_generate_key_pair(
    uint8_t randomness[64U]) {
  libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_b1_ed();
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_avx2_unpacked_generate_key_pair_mut(uu____0,
                                                              &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_avx2_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_b1_ed();
}

/**
 Create a new, empty unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
libcrux_ml_kem_mlkem768_avx2_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_3f_ed();
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_sampling_sample_from_xof_51(
    Eurydice_slice seeds, Eurydice_slice sampled_coefficients,
    Eurydice_slice out) {
  libcrux_ml_kem_hash_functions_portable_PortableHash xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_6e(
          seeds);
  uint8_t randomness[3U][504U] = {{0U}};
  uint8_t randomness_blocksize[3U][168U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_6e(
      &xof_state,
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]));
  bool done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed(
      Eurydice_array_to_slice((size_t)3U, randomness, uint8_t[504U]),
      sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_6e(
          &xof_state, Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                              uint8_t[168U]));
      done = libcrux_ml_kem_sampling_sample_from_uniform_distribution_next_ed0(
          Eurydice_array_to_slice((size_t)3U, randomness_blocksize,
                                  uint8_t[168U]),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_ml_kem_matrix_sample_matrix_A_51(
    Eurydice_slice A_transpose, uint8_t *seed, bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_seed[34U];
    memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
    uint8_t seeds[3U][34U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      memcpy(seeds[i], copy_of_seed, (size_t)34U * sizeof(uint8_t));
    }
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds[j][32U] = (uint8_t)i1;
      seeds[j][33U] = (uint8_t)j;
    }
    size_t sampled_coefficients[3U] = {0U};
    int16_t out[3U][272U] = {{0U}};
    libcrux_ml_kem_sampling_sample_from_xof_51(
        Eurydice_array_to_slice((size_t)3U, seeds, uint8_t[34U]),
        Eurydice_array_to_slice((size_t)3U, sampled_coefficients, size_t),
        Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]));
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, out, int16_t[272U]),
                 int16_t[272U]);
         i++) {
      size_t j = i;
      int16_t sample[272U];
      memcpy(sample, out[j], (size_t)272U * sizeof(int16_t));
      if (transpose) {
        Eurydice_slice uu____1 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_06(
            uu____1, &Eurydice_slice_index(
                         A_transpose, j * (size_t)3U + i1,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
      } else {
        Eurydice_slice uu____2 = Eurydice_array_to_subslice_to(
            (size_t)272U, sample, (size_t)256U, int16_t, size_t, int16_t[]);
        libcrux_ml_kem_polynomial_from_i16_array_d6_06(
            uu____2, &Eurydice_slice_index(
                         A_transpose, i1 * (size_t)3U + j,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6,
                         libcrux_ml_kem_polynomial_PolynomialRingElement_f6 *));
      }
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_avx2_SIMD256Vector,
libcrux_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_fd(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_ab(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, unpacked_public_key->t_as_ntt,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_slice uu____1 = Eurydice_array_to_slice(
      (size_t)9U, unpacked_public_key->A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  libcrux_ml_kem_matrix_sample_matrix_A_51(uu____1, ret, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_e2(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  libcrux_ml_kem_ind_cpa_deserialize_vector_ab(
      ind_cpa_secret_key,
      Eurydice_array_to_slice(
          (size_t)3U, key_pair->private_key.ind_cpa_private_key.secret_as_ntt,
          libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  libcrux_ml_kem_ind_cpa_build_unpacked_public_key_mut_fd(
      ind_cpa_public_key, &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1152U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.keypair_from_private_key
with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_keypair_from_private_key_ce(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_e2(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_from_private_mut(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_keypair_from_private_key_ce(
      private_key, key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_b1 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_2f(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  uint8_t ind_cpa_private_key[1152U] = {0U};
  uint8_t ind_cpa_public_key[1184U] = {0U};
  __m256i scratch = libcrux_ml_kem_vector_avx2_ZERO_f5();
  libcrux_ml_kem_ind_cpa_serialize_unpacked_secret_key_8c(
      &self->public_key.ind_cpa_public_key,
      &self->private_key.ind_cpa_private_key,
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      &scratch);
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_1f(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_b1 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_b1_2f(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk =
      libcrux_ml_kem_types_default_d3_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_2f(self, &sk);
  return sk;
}

/**
 Get the serialized private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_b1_2f(key_pair);
}

/**
 Get the serialized private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_b1_2f(key_pair,
                                                                   serialized);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_6a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_6a_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *self) {
  uint8_t public_key[1184U] = {0U};
  __m256i scratch = libcrux_ml_kem_vector_avx2_ZERO_f5();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t), &scratch);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_fd_d0(copy_of_public_key);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_b1 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_b1_ed(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_6a_ed(&self->public_key);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_b1_ed(key_pair);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_6a
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  __m256i scratch = libcrux_ml_kem_vector_avx2_ZERO_f5();
  libcrux_ml_kem_ind_cpa_serialize_public_key_mut_ed(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      Eurydice_array_to_slice((size_t)1184U, serialized->value, uint8_t),
      &scratch);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_b1 with types
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_b1_ed(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_ed(&self->public_key,
                                                       serialized);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem768_avx2_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_b1_ed(key_pair,
                                                                  serialized);
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_1c
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0
libcrux_ml_kem_ind_cpa_unpacked_clone_1c_ed(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 uu____0[3U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)3U, self->t_as_ntt, uu____0,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6, void *);
  uint8_t uu____1[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->seed_for_A, uu____1, uint8_t, void *);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_c0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_f6 ret[9U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)9U, self->A, ret,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6, void *);
  memcpy(
      lit.A, ret,
      (size_t)9U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  return lit;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_86
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
libcrux_ml_kem_ind_cca_unpacked_clone_86_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *self) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 lit;
  lit.ind_cpa_public_key =
      libcrux_ml_kem_ind_cpa_unpacked_clone_1c_ed(&self->ind_cpa_public_key);
  uint8_t ret[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->public_key_hash, ret, uint8_t, void *);
  memcpy(lit.public_key_hash, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_b1
with types libcrux_ml_kem_vector_avx2_SIMD256Vector
with const generics
- K= 3
- K_SQUARED= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *
libcrux_ml_kem_ind_cca_unpacked_public_key_b1_ed(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
 Get the unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_public_key(
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *pk) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 uu____0 =
      libcrux_ml_kem_ind_cca_unpacked_clone_86_ed(
          libcrux_ml_kem_ind_cca_unpacked_public_key_b1_ed(key_pair));
  pk[0U] = uu____0;
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0 *public_key,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_6a_ed(public_key, serialized);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_avx2_Simd256Hash,
libcrux_ml_kem_vector_avx2_SIMD256Vector with const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_6d(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
        *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice_to((size_t)1184U, public_key->value,
                                    (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_serialize_deserialize_ring_elements_reduced_ab(
      uu____0, Eurydice_array_to_slice(
                   (size_t)3U, unpacked_public_key->ind_cpa_public_key.t_as_ntt,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_f6));
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_slice(
      (size_t)9U, unpacked_public_key->ind_cpa_public_key.A,
      libcrux_ml_kem_polynomial_PolynomialRingElement_f6);
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      ret);
  libcrux_ml_kem_matrix_sample_matrix_A_6c(uu____2, ret, false);
  libcrux_ml_kem_hash_functions_avx2_H_26(
      Eurydice_array_to_slice((size_t)1184U,
                              libcrux_ml_kem_types_as_slice_e6_d0(public_key),
                              uint8_t),
      Eurydice_array_to_slice((size_t)32U, unpacked_public_key->public_key_hash,
                              uint8_t));
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.unpack_public_key_avx2 with
const generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_avx2_a5(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_6d(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.unpack_public_key with const
generics
- K= 3
- K_SQUARED= 9
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_a5(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_avx2_a5(
      public_key, unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem768_avx2_unpacked_unpacked_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_a5(
      public_key, unpacked_public_key);
}

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_c0
    libcrux_ml_kem_mlkem768_avx2_unpacked_MlKem768PublicKeyUnpacked;

#define libcrux_mlkem768_avx2_H_DEFINED
#endif /* libcrux_mlkem768_avx2_H */
