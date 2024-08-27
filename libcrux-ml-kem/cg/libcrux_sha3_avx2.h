/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f39fa18bb6efe2199d17b8f79b10d4127d24289
 * Eurydice: cd5c9e55b3c032977eccf22edd8a91b4b02e338e
 * Karamel: 2dfc25438318f1d832ad6d2d2b595cb870466fc3
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 919a6a57fe3548db83f6416d540116c2c8a9f2c1
 */

#ifndef __libcrux_sha3_avx2_H
#define __libcrux_sha3_avx2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_core.h"
#include "libcrux_sha3_portable.h"

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_zero_ef(void) {
  return libcrux_intrinsics_avx2_mm256_set1_epi64x((int64_t)0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__veor5q_u64(
    __m256i a, __m256i b, __m256i c, __m256i d, __m256i e) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  __m256i cd = libcrux_intrinsics_avx2_mm256_xor_si256(c, d);
  __m256i abcd = libcrux_intrinsics_avx2_mm256_xor_si256(ab, cd);
  return libcrux_intrinsics_avx2_mm256_xor_si256(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_xor5_ef(
    __m256i a, __m256i b, __m256i c, __m256i d, __m256i e) {
  return libcrux_sha3_simd_avx2__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_58(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)1, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)63, x, __m256i));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vrax1q_u64(__m256i a,
                                                                  __m256i b) {
  __m256i uu____0 = a;
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      uu____0, libcrux_sha3_simd_avx2_rotate_left_58(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vrax1q_u64(a, b);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vbcaxq_u64(__m256i a,
                                                                  __m256i b,
                                                                  __m256i c) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      a, libcrux_intrinsics_avx2_mm256_andnot_si256(c, b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_and_not_xor_ef(__m256i a, __m256i b, __m256i c) {
  return libcrux_sha3_simd_avx2__vbcaxq_u64(a, b, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__veorq_n_u64(__m256i a,
                                                                   uint64_t c) {
  __m256i c0 = libcrux_intrinsics_avx2_mm256_set1_epi64x((int64_t)c);
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_constant_ef(__m256i a, uint64_t c) {
  return libcrux_sha3_simd_avx2__veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_xor_ef(__m256i a,
                                                             __m256i b) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_slice_4(
    Eurydice_slice a[4U], size_t start, size_t len, Eurydice_slice ret[4U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t);
  ret[1U] = Eurydice_slice_subslice2(a[1U], start, start + len, uint8_t);
  ret[2U] = Eurydice_slice_subslice2(a[2U], start, start + len, uint8_t);
  ret[3U] = Eurydice_slice_subslice2(a[3U], start, start + len, uint8_t);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_slice_n_ef(
    Eurydice_slice a[4U], size_t start, size_t len, Eurydice_slice ret[4U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_a[4U];
  memcpy(copy_of_a, a, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[4U];
  libcrux_sha3_simd_avx2_slice_4(copy_of_a, start, len, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(Eurydice_slice));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Eurydice_slice_uint8_t_4size_t__x2
libcrux_sha3_simd_avx2_split_at_mut_4(Eurydice_slice out[4U], size_t mid) {
  Eurydice_slice out0 = out[0U];
  Eurydice_slice out1 = out[1U];
  Eurydice_slice out2 = out[2U];
  Eurydice_slice out3 = out[3U];
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at_mut(
      out0, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at_mut(
      out1, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out10 = uu____1.fst;
  Eurydice_slice out11 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at_mut(
      out2, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out20 = uu____2.fst;
  Eurydice_slice out21 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = Eurydice_slice_split_at_mut(
      out3, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out30 = uu____3.fst;
  Eurydice_slice out31 = uu____3.snd;
  Eurydice_slice_uint8_t_4size_t__x2 lit;
  lit.fst[0U] = out00;
  lit.fst[1U] = out10;
  lit.fst[2U] = out20;
  lit.fst[3U] = out30;
  lit.snd[0U] = out01;
  lit.snd[1U] = out11;
  lit.snd[2U] = out21;
  lit.snd[3U] = out31;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Eurydice_slice_uint8_t_4size_t__x2
libcrux_sha3_simd_avx2_split_at_mut_n_ef(Eurydice_slice a[4U], size_t mid) {
  return libcrux_sha3_simd_avx2_split_at_mut_4(a, mid);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types core_core_arch_x86___m256i
with const generics
- $4size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_29_s {
  __m256i st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_29;

/**
 Create a new Shake128 x4 state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_1e
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_29
libcrux_sha3_generic_keccak_new_1e_bf(void) {
  libcrux_sha3_generic_keccak_KeccakState_29 lit;
  lit.st[0U][0U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[0U][1U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[0U][2U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[0U][3U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[0U][4U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[1U][0U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[1U][1U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[1U][2U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[1U][3U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[1U][4U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[2U][0U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[2U][1U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[2U][2U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[2U][3U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[2U][4U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[3U][0U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[3U][1U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[3U][2U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[3U][3U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[3U][4U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[4U][0U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[4U][1U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[4U][2U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[4U][3U] = libcrux_sha3_simd_avx2_zero_ef();
  lit.st[4U][4U] = libcrux_sha3_simd_avx2_zero_ef();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_c7(
    __m256i (*s)[5U], Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v00 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v10 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v20 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v30 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v0l = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, v1h, v3h, __m256i);
    s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U] =
        libcrux_intrinsics_avx2_mm256_xor_si256(
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U], v0);
    s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
             v1);
    s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)2U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
             v2);
    s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)3U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
             v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_slice_subslice2(blocks[0U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____1 =
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t);
  Eurydice_slice_copy(
      uu____1,
      Eurydice_slice_subslice2(blocks[1U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____2 =
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t);
  Eurydice_slice_copy(
      uu____2,
      Eurydice_slice_subslice2(blocks[2U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____3 =
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t);
  Eurydice_slice_copy(
      uu____3,
      Eurydice_slice_subslice2(blocks[3U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  __m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N__23__as_slice((size_t)32U, u8s, uint8_t,
                                            Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i0][j0], u);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice uu____4 =
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t);
    Eurydice_slice_copy(uu____4,
                        Eurydice_slice_subslice2(blocks[0U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____5 =
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t);
    Eurydice_slice_copy(uu____5,
                        Eurydice_slice_subslice2(blocks[1U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____6 =
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t);
    Eurydice_slice_copy(uu____6,
                        Eurydice_slice_subslice2(blocks[2U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____7 =
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t);
    Eurydice_slice_copy(uu____7,
                        Eurydice_slice_subslice2(blocks[3U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    __m256i u0 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        core_array___Array_T__N__23__as_slice((size_t)32U, u8s0, uint8_t,
                                              Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    s[i][j] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i][j], u0);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_ef
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_ef_65(
    __m256i (*a)[5U], Eurydice_slice b[4U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[4U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_avx2_load_block_c7(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_580(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)36, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)28, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_c1(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_580(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_17(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_581(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)3, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)61, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c10(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_581(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_170(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_582(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)41, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)23, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c11(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_582(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_171(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_583(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)18, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)46, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c12(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_583(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_172(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c13(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_58(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_173(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_584(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)44, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)20, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c14(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_584(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_174(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_585(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)10, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)54, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c15(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_585(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_175(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_586(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)45, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)19, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c16(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_586(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_176(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_587(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)2, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)62, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c17(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_587(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_177(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_588(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)62, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)2, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c18(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_588(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_178(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_589(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)6, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)58, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c19(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_589(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_179(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5810(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)43, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)21, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c110(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5810(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1710(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c110(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5811(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)15, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)49, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c111(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5811(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1711(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c111(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5812(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)61, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)3, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c112(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5812(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1712(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c112(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5813(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)28, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)36, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c113(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5813(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1713(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c113(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5814(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)55, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)9, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c114(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5814(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1714(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c114(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5815(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)25, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)39, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c115(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5815(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1715(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c115(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5816(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)21, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)43, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c116(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5816(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1716(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c116(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5817(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)56, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)8, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c117(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5817(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1717(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c117(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5818(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)27, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)37, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c118(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5818(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1718(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c118(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5819(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)20, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)44, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c119(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5819(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1719(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c119(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5820(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)39, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)25, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c120(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5820(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1720(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c120(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5821(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)8, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)56, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c121(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5821(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1721(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c121(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5822(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)14, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)50, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2__vxarq_u64_c122(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5822(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_ef
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1722(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c122(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_74(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  __m256i c[5U] = {libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][0U], s->st[1U][0U],
                                                  s->st[2U][0U], s->st[3U][0U],
                                                  s->st[4U][0U]),
                   libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][1U], s->st[1U][1U],
                                                  s->st[2U][1U], s->st[3U][1U],
                                                  s->st[4U][1U]),
                   libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][2U], s->st[1U][2U],
                                                  s->st[2U][2U], s->st[3U][2U],
                                                  s->st[4U][2U]),
                   libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][3U], s->st[1U][3U],
                                                  s->st[2U][3U], s->st[3U][3U],
                                                  s->st[4U][3U]),
                   libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][4U], s->st[1U][4U],
                                                  s->st[2U][4U], s->st[3U][4U],
                                                  s->st[4U][4U])};
  __m256i uu____0 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
      c[((size_t)0U + (size_t)4U) % (size_t)5U],
      c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  __m256i uu____1 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
      c[((size_t)1U + (size_t)4U) % (size_t)5U],
      c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  __m256i uu____2 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
      c[((size_t)2U + (size_t)4U) % (size_t)5U],
      c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  __m256i uu____3 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
      c[((size_t)3U + (size_t)4U) % (size_t)5U],
      c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  __m256i t[5U] = {uu____0, uu____1, uu____2, uu____3,
                   libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
                       c[((size_t)4U + (size_t)4U) % (size_t)5U],
                       c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = libcrux_sha3_simd_avx2_xor_ef(s->st[0U][0U], t[0U]);
  s->st[1U][0U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_17(s->st[1U][0U], t[0U]);
  s->st[2U][0U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_170(s->st[2U][0U], t[0U]);
  s->st[3U][0U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_171(s->st[3U][0U], t[0U]);
  s->st[4U][0U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_172(s->st[4U][0U], t[0U]);
  s->st[0U][1U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_173(s->st[0U][1U], t[1U]);
  s->st[1U][1U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_174(s->st[1U][1U], t[1U]);
  s->st[2U][1U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_175(s->st[2U][1U], t[1U]);
  s->st[3U][1U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_176(s->st[3U][1U], t[1U]);
  s->st[4U][1U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_177(s->st[4U][1U], t[1U]);
  s->st[0U][2U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_178(s->st[0U][2U], t[2U]);
  s->st[1U][2U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_179(s->st[1U][2U], t[2U]);
  s->st[2U][2U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1710(s->st[2U][2U], t[2U]);
  s->st[3U][2U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1711(s->st[3U][2U], t[2U]);
  s->st[4U][2U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1712(s->st[4U][2U], t[2U]);
  s->st[0U][3U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1713(s->st[0U][3U], t[3U]);
  s->st[1U][3U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1714(s->st[1U][3U], t[3U]);
  s->st[2U][3U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1715(s->st[2U][3U], t[3U]);
  s->st[3U][3U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1716(s->st[3U][3U], t[3U]);
  s->st[4U][3U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1717(s->st[4U][3U], t[3U]);
  s->st[0U][4U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1718(s->st[0U][4U], t[4U]);
  s->st[1U][4U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1719(s->st[1U][4U], t[4U]);
  s->st[2U][4U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1720(s->st[2U][4U], t[4U]);
  s->st[3U][4U] =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1721(s->st[3U][4U], t[4U]);
  __m256i uu____27 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1722(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_35(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  __m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(__m256i[5U]));
  s->st[0U][1U] = old[1U][1U];
  s->st[0U][2U] = old[2U][2U];
  s->st[0U][3U] = old[3U][3U];
  s->st[0U][4U] = old[4U][4U];
  s->st[1U][0U] = old[0U][3U];
  s->st[1U][1U] = old[1U][4U];
  s->st[1U][2U] = old[2U][0U];
  s->st[1U][3U] = old[3U][1U];
  s->st[1U][4U] = old[4U][2U];
  s->st[2U][0U] = old[0U][1U];
  s->st[2U][1U] = old[1U][2U];
  s->st[2U][2U] = old[2U][3U];
  s->st[2U][3U] = old[3U][4U];
  s->st[2U][4U] = old[4U][0U];
  s->st[3U][0U] = old[0U][4U];
  s->st[3U][1U] = old[1U][0U];
  s->st[3U][2U] = old[2U][1U];
  s->st[3U][3U] = old[3U][2U];
  s->st[3U][4U] = old[4U][3U];
  s->st[4U][0U] = old[0U][2U];
  s->st[4U][1U] = old[1U][3U];
  s->st[4U][2U] = old[2U][4U];
  s->st[4U][3U] = old[3U][0U];
  s->st[4U][4U] = old[4U][1U];
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_09(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  __m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(__m256i[5U]));
  for (size_t i0 = (size_t)0U; i0 < (size_t)5U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t j = i;
      s->st[i1][j] = libcrux_sha3_simd_avx2_and_not_xor_ef(
          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
          old[i1][(j + (size_t)1U) % (size_t)5U]);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_5b(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, size_t i) {
  s->st[0U][0U] = libcrux_sha3_simd_avx2_xor_constant_ef(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_f8(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_74(s);
    libcrux_sha3_generic_keccak_pi_35(s);
    libcrux_sha3_generic_keccak_chi_09(s);
    libcrux_sha3_generic_keccak_iota_5b(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_1d(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice blocks[4U]) {
  __m256i(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[4U];
  memcpy(uu____1, blocks, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_avx2_load_block_ef_65(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_f8(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_91(
    __m256i (*s)[5U], uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_c7(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full_ef
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_e9(
    __m256i (*a)[5U], uint8_t b[4U][200U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[4U][200U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_91(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_d9(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice last[4U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  __m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_ef_e9(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_f8(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_e9(
    __m256i (*s)[5U], Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32,
        s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49,
        s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t), s[i0][j0]);
  Eurydice_slice uu____0 =
      Eurydice_slice_subslice2(out[0U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____1 =
      Eurydice_slice_subslice2(out[1U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____1,
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t),
      uint8_t);
  Eurydice_slice uu____2 =
      Eurydice_slice_subslice2(out[2U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____2,
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t),
      uint8_t);
  Eurydice_slice uu____3 =
      Eurydice_slice_subslice2(out[3U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____3,
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t),
      uint8_t);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t), s[i][j]);
    Eurydice_slice uu____4 = Eurydice_slice_subslice2(
        out[0U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____4,
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t),
        uint8_t);
    Eurydice_slice uu____5 = Eurydice_slice_subslice2(
        out[1U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____5,
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t),
        uint8_t);
    Eurydice_slice uu____6 = Eurydice_slice_subslice2(
        out[2U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____6,
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t),
        uint8_t);
    Eurydice_slice uu____7 = Eurydice_slice_subslice2(
        out[3U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____7,
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_full
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_0b(
    __m256i (*s)[5U], uint8_t ret[4U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  uint8_t out2[200U] = {0U};
  uint8_t out3[200U] = {0U};
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out3, uint8_t)};
  libcrux_sha3_simd_avx2_store_block_e9(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[200U];
  memcpy(copy_of_out0, out0, (size_t)200U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[200U];
  memcpy(copy_of_out1, out1, (size_t)200U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[200U];
  memcpy(copy_of_out2, out2, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____3[200U];
  memcpy(uu____3, out3, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], copy_of_out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[2U], copy_of_out2, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[3U], uu____3, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_full_ef
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_ef_43(
    __m256i (*a)[5U], uint8_t ret[4U][200U]) {
  libcrux_sha3_simd_avx2_store_block_full_0b(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c54(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  uint8_t b[4U][200U];
  libcrux_sha3_simd_avx2_store_block_full_ef_43(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_ef
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_58(
    __m256i (*a)[5U], Eurydice_slice b[4U]) {
  libcrux_sha3_simd_avx2_store_block_e9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_9b(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_simd_avx2_store_block_ef_58(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_b4(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_f8(s);
  libcrux_sha3_simd_avx2_store_block_ef_58(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_74(
    libcrux_sha3_generic_keccak_KeccakState_29 s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_f8(&s);
  uint8_t b[4U][200U];
  libcrux_sha3_simd_avx2_store_block_full_ef_43(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_4f(
    Eurydice_slice data[4U], Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_KeccakState_29 s =
      libcrux_sha3_generic_keccak_new_1e_bf();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_29 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[4U];
    memcpy(copy_of_data, data, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice ret[4U];
    libcrux_sha3_simd_avx2_slice_n_ef(copy_of_data, i0 * (size_t)136U,
                                      (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_1d(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_29 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[4U];
  memcpy(copy_of_data, data, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret[4U];
  libcrux_sha3_simd_avx2_slice_n_ef(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_d9(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c54(&s, out);
  } else {
    Eurydice_slice_uint8_t_4size_t__x2 uu____4 =
        libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)136U);
    Eurydice_slice o0[4U];
    memcpy(o0, uu____4.fst, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice o1[4U];
    memcpy(o1, uu____4.snd, (size_t)4U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_9b(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, Option_b3)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_4size_t__x2 uu____5 =
            libcrux_sha3_simd_avx2_split_at_mut_n_ef(o1, (size_t)136U);
        Eurydice_slice o[4U];
        memcpy(o, uu____5.fst, (size_t)4U * sizeof(Eurydice_slice));
        Eurydice_slice orest[4U];
        memcpy(orest, uu____5.snd, (size_t)4U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_b4(&s, o);
        memcpy(o1, orest, (size_t)4U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_74(s, o1);
    }
  }
}

/**
 Perform 4 SHAKE256 operations in parallel
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_avx2_x4_shake256(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf0[4U] = {input0, input1, input2, input3};
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_keccak_4f(buf0, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_29
    libcrux_sha3_avx2_x4_incremental_KeccakState;

/**
 Initialise the [`KeccakState`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_29
libcrux_sha3_avx2_x4_incremental_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_bf();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_c70(
    __m256i (*s)[5U], Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v00 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v10 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v20 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v30 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v0l = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, v1h, v3h, __m256i);
    s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U] =
        libcrux_intrinsics_avx2_mm256_xor_si256(
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U], v0);
    s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
             v1);
    s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)2U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
             v2);
    s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)3U) % (size_t)5U] =
         libcrux_intrinsics_avx2_mm256_xor_si256(
             s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
              [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
             v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_slice_subslice2(blocks[0U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____1 =
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t);
  Eurydice_slice_copy(
      uu____1,
      Eurydice_slice_subslice2(blocks[1U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____2 =
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t);
  Eurydice_slice_copy(
      uu____2,
      Eurydice_slice_subslice2(blocks[2U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____3 =
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t);
  Eurydice_slice_copy(
      uu____3,
      Eurydice_slice_subslice2(blocks[3U], start, start + (size_t)8U, uint8_t),
      uint8_t);
  __m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N__23__as_slice((size_t)32U, u8s, uint8_t,
                                            Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i0][j0], u);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice uu____4 =
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t);
    Eurydice_slice_copy(uu____4,
                        Eurydice_slice_subslice2(blocks[0U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____5 =
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t);
    Eurydice_slice_copy(uu____5,
                        Eurydice_slice_subslice2(blocks[1U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____6 =
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t);
    Eurydice_slice_copy(uu____6,
                        Eurydice_slice_subslice2(blocks[2U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    Eurydice_slice uu____7 =
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t);
    Eurydice_slice_copy(uu____7,
                        Eurydice_slice_subslice2(blocks[3U], start + (size_t)8U,
                                                 start + (size_t)16U, uint8_t),
                        uint8_t);
    __m256i u0 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        core_array___Array_T__N__23__as_slice((size_t)32U, u8s0, uint8_t,
                                              Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    s[i][j] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i][j], u0);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_910(
    __m256i (*s)[5U], uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_c70(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full_ef
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_e90(
    __m256i (*a)[5U], uint8_t b[4U][200U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[4U][200U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_910(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_d90(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice last[4U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)168U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  __m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_ef_e90(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_f8(s);
}

/**
 Absorb
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_d90(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_e90(
    __m256i (*s)[5U], Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32,
        s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49,
        s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t), s[i0][j0]);
  Eurydice_slice uu____0 =
      Eurydice_slice_subslice2(out[0U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t),
      uint8_t);
  Eurydice_slice uu____1 =
      Eurydice_slice_subslice2(out[1U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____1,
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t),
      uint8_t);
  Eurydice_slice uu____2 =
      Eurydice_slice_subslice2(out[2U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____2,
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t),
      uint8_t);
  Eurydice_slice uu____3 =
      Eurydice_slice_subslice2(out[3U], start, start + (size_t)8U, uint8_t);
  Eurydice_slice_copy(
      uu____3,
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t),
      uint8_t);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t), s[i][j]);
    Eurydice_slice uu____4 = Eurydice_slice_subslice2(
        out[0U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____4,
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t),
        uint8_t);
    Eurydice_slice uu____5 = Eurydice_slice_subslice2(
        out[1U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____5,
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t),
        uint8_t);
    Eurydice_slice uu____6 = Eurydice_slice_subslice2(
        out[2U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____6,
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t),
        uint8_t);
    Eurydice_slice uu____7 = Eurydice_slice_subslice2(
        out[3U], start + (size_t)8U, start + (size_t)16U, uint8_t);
    Eurydice_slice_copy(
        uu____7,
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_ef
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_580(
    __m256i (*a)[5U], Eurydice_slice b[4U]) {
  libcrux_sha3_simd_avx2_store_block_e90(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_b40(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_f8(s);
  libcrux_sha3_simd_avx2_store_block_ef_580(s->st, out);
}

/**
 Squeeze another block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_9b0(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_simd_avx2_store_block_ef_580(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_2a(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_9b0(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o2[4U];
  memcpy(o2, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o2);
}

/**
 Squeeze three blocks
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_2a(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_69(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_9b0(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o20[4U];
  memcpy(o20, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o1);
  Eurydice_slice_uint8_t_4size_t__x2 uu____2 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o20, (size_t)168U);
  Eurydice_slice o2[4U];
  memcpy(o2, uu____2.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o30[4U];
  memcpy(o30, uu____2.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o2);
  Eurydice_slice_uint8_t_4size_t__x2 uu____3 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o30, (size_t)168U);
  Eurydice_slice o3[4U];
  memcpy(o3, uu____3.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o4[4U];
  memcpy(o4, uu____3.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_b40(s, o4);
}

/**
 Squeeze five blocks
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_69(s, buf);
}

/**
 Absorb
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_d9(s, buf);
}

/**
 Squeeze block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_block_9b(s, buf);
}

/**
 Squeeze next block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_b4(s, buf);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
