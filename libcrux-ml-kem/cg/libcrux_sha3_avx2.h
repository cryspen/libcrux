/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: 3ed3c98d39ce028c31c5908a38bc68ad5098f563
 * Libcrux: aa91a6764bde8c1f15107a03746f506e99a9159b
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_zero_ef(void) {
  return libcrux_intrinsics_avx2_mm256_set1_epi64x((int64_t)0);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__veor5q_u64(core_core_arch_x86___m256i a,
                                   core_core_arch_x86___m256i b,
                                   core_core_arch_x86___m256i c,
                                   core_core_arch_x86___m256i d,
                                   core_core_arch_x86___m256i e) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  core_core_arch_x86___m256i cd = libcrux_intrinsics_avx2_mm256_xor_si256(c, d);
  core_core_arch_x86___m256i abcd =
      libcrux_intrinsics_avx2_mm256_xor_si256(ab, cd);
  return libcrux_intrinsics_avx2_mm256_xor_si256(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor5_ef(core_core_arch_x86___m256i a,
                               core_core_arch_x86___m256i b,
                               core_core_arch_x86___m256i c,
                               core_core_arch_x86___m256i d,
                               core_core_arch_x86___m256i e) {
  return libcrux_sha3_simd_avx2__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_58(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)1, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)63, x,
                                               core_core_arch_x86___m256i));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vrax1q_u64(core_core_arch_x86___m256i a,
                                   core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i uu____0 = a;
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      uu____0, libcrux_sha3_simd_avx2_rotate_left_58(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(core_core_arch_x86___m256i a,
                                               core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vrax1q_u64(a, b);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vbcaxq_u64(core_core_arch_x86___m256i a,
                                   core_core_arch_x86___m256i b,
                                   core_core_arch_x86___m256i c) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      a, libcrux_intrinsics_avx2_mm256_andnot_si256(c, b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_and_not_xor_ef(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b,
                                      core_core_arch_x86___m256i c) {
  return libcrux_sha3_simd_avx2__vbcaxq_u64(a, b, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__veorq_n_u64(core_core_arch_x86___m256i a, uint64_t c) {
  core_core_arch_x86___m256i c0 =
      libcrux_intrinsics_avx2_mm256_set1_epi64x((int64_t)c);
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_constant_ef(core_core_arch_x86___m256i a,
                                       uint64_t c) {
  return libcrux_sha3_simd_avx2__veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i libcrux_sha3_simd_avx2_xor_ef(
    core_core_arch_x86___m256i a, core_core_arch_x86___m256i b) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_slice_4(
    Eurydice_slice a[4U], size_t start, size_t len, Eurydice_slice ret[4U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t,
                                     Eurydice_slice);
  ret[1U] = Eurydice_slice_subslice2(a[1U], start, start + len, uint8_t,
                                     Eurydice_slice);
  ret[2U] = Eurydice_slice_subslice2(a[2U], start, start + len, uint8_t,
                                     Eurydice_slice);
  ret[3U] = Eurydice_slice_subslice2(a[3U], start, start + len, uint8_t,
                                     Eurydice_slice);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_slice_n_ef(
    Eurydice_slice a[4U], size_t start, size_t len, Eurydice_slice ret[4U]) {
  Eurydice_slice uu____0[4U];
  memcpy(uu____0, a, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[4U];
  libcrux_sha3_simd_avx2_slice_4(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(Eurydice_slice));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE Eurydice_slice_uint8_t_4size_t__x2
libcrux_sha3_simd_avx2_split_at_mut_4(Eurydice_slice out[4U], size_t mid) {
  Eurydice_slice out0 = out[0U];
  Eurydice_slice out1 = out[1U];
  Eurydice_slice out2 = out[2U];
  Eurydice_slice out3 = out[3U];
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at_mut(
      out0, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at_mut(
      out1, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out10 = uu____1.fst;
  Eurydice_slice out11 = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = core_slice___Slice_T___split_at_mut(
      out2, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out20 = uu____2.fst;
  Eurydice_slice out21 = uu____2.snd;
  Eurydice_slice_uint8_t_x2 uu____3 = core_slice___Slice_T___split_at_mut(
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
  core_core_arch_x86___m256i st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_29;

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
libcrux_sha3_generic_keccak_new_1e_16(void) {
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
    core_core_arch_x86___m256i (*s)[5U], Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[0U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[1U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[2U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[3U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v0l =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v00, v10);
    core_core_arch_x86___m256i v1h =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v00, v10);
    core_core_arch_x86___m256i v2l =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v20, v30);
    core_core_arch_x86___m256i v3h =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v20, v30);
    core_core_arch_x86___m256i v0 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32, v0l, v2l, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v1 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32, v1h, v3h, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v2 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49, v0l, v2l, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v3 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49, v1h, v3h, core_core_arch_x86___m256i);
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
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      u8s, (size_t)0U, (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_slice_subslice2(blocks[0U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
      u8s, (size_t)8U, (size_t)16U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____1,
      Eurydice_slice_subslice2(blocks[1U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
      u8s, (size_t)16U, (size_t)24U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_slice_subslice2(blocks[2U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
      u8s, (size_t)24U, (size_t)32U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_slice_subslice2(blocks[3U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  core_core_arch_x86___m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N__23__as_slice((size_t)32U, u8s, uint8_t,
                                            Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i0][j0], u);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice uu____4 = Eurydice_array_to_subslice2(
        u8s0, (size_t)0U, (size_t)8U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____4,
        Eurydice_slice_subslice2(blocks[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____5 = Eurydice_array_to_subslice2(
        u8s0, (size_t)8U, (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____5,
        Eurydice_slice_subslice2(blocks[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
        u8s0, (size_t)16U, (size_t)24U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____6,
        Eurydice_slice_subslice2(blocks[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____7 = Eurydice_array_to_subslice2(
        u8s0, (size_t)24U, (size_t)32U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____7,
        Eurydice_slice_subslice2(blocks[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    core_core_arch_x86___m256i u0 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
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
- BLOCKSIZE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_ef_6a(
    core_core_arch_x86___m256i (*a)[5U], Eurydice_slice b[4U]) {
  core_core_arch_x86___m256i(*uu____0)[5U] = a;
  Eurydice_slice uu____1[4U];
  memcpy(uu____1, b, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_avx2_load_block_c7(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_580(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)36, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)28, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c1(core_core_arch_x86___m256i a,
                                     core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_17(core_core_arch_x86___m256i a,
                                            core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_581(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)3, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)61, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c10(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_170(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_582(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)41, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)23, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c11(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_171(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_583(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)18, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)46, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c12(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_172(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c13(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_173(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_584(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)44, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)20, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c14(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_174(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_585(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)10, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)54, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c15(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_175(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_586(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)45, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)19, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c16(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_176(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_587(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)2, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)62, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c17(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_177(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_588(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)62, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)2, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c18(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_178(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_589(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)6, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)58, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c19(core_core_arch_x86___m256i a,
                                      core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_179(core_core_arch_x86___m256i a,
                                             core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5810(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)43, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)21, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c110(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1710(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c110(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5811(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)15, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)49, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c111(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1711(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c111(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5812(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)61, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)3, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c112(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1712(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c112(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5813(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)28, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)36, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c113(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1713(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c113(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5814(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)55, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)9, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c114(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1714(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c114(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5815(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)25, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)39, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c115(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1715(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c115(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5816(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)21, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)43, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c116(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1716(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c116(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5817(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)56, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)8, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c117(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1717(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c117(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5818(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)27, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)37, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c118(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1718(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c118(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5819(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)20, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)44, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c119(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1719(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c119(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5820(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)39, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)25, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c120(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1720(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c120(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5821(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)8, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)56, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c121(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1721(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c121(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_rotate_left_5822(core_core_arch_x86___m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)14, x,
                                               core_core_arch_x86___m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)50, x,
                                               core_core_arch_x86___m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2__vxarq_u64_c122(core_core_arch_x86___m256i a,
                                       core_core_arch_x86___m256i b) {
  core_core_arch_x86___m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
static KRML_MUSTINLINE core_core_arch_x86___m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_1722(core_core_arch_x86___m256i a,
                                              core_core_arch_x86___m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_c122(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_71(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  core_core_arch_x86___m256i c[5U] = {
      libcrux_sha3_simd_avx2_xor5_ef(s->st[0U][0U], s->st[1U][0U],
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
  core_core_arch_x86___m256i uu____0 =
      libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
          c[((size_t)0U + (size_t)4U) % (size_t)5U],
          c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  core_core_arch_x86___m256i uu____1 =
      libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
          c[((size_t)1U + (size_t)4U) % (size_t)5U],
          c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  core_core_arch_x86___m256i uu____2 =
      libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
          c[((size_t)2U + (size_t)4U) % (size_t)5U],
          c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  core_core_arch_x86___m256i uu____3 =
      libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
          c[((size_t)3U + (size_t)4U) % (size_t)5U],
          c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  core_core_arch_x86___m256i t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      libcrux_sha3_simd_avx2_rotate_left1_and_xor_ef(
          c[((size_t)4U + (size_t)4U) % (size_t)5U],
          c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = libcrux_sha3_simd_avx2_xor_ef(s->st[0U][0U], t[0U]);
  core_core_arch_x86___m256i uu____4 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_17(s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  core_core_arch_x86___m256i uu____5 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_170(s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  core_core_arch_x86___m256i uu____6 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_171(s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  core_core_arch_x86___m256i uu____7 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_172(s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  core_core_arch_x86___m256i uu____8 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_173(s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  core_core_arch_x86___m256i uu____9 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_174(s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  core_core_arch_x86___m256i uu____10 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_175(s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  core_core_arch_x86___m256i uu____11 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_176(s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  core_core_arch_x86___m256i uu____12 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_177(s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  core_core_arch_x86___m256i uu____13 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_178(s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  core_core_arch_x86___m256i uu____14 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_179(s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  core_core_arch_x86___m256i uu____15 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1710(s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  core_core_arch_x86___m256i uu____16 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1711(s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  core_core_arch_x86___m256i uu____17 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1712(s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  core_core_arch_x86___m256i uu____18 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1713(s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  core_core_arch_x86___m256i uu____19 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1714(s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  core_core_arch_x86___m256i uu____20 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1715(s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  core_core_arch_x86___m256i uu____21 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1716(s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  core_core_arch_x86___m256i uu____22 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1717(s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  core_core_arch_x86___m256i uu____23 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1718(s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  core_core_arch_x86___m256i uu____24 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1719(s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  core_core_arch_x86___m256i uu____25 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1720(s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  core_core_arch_x86___m256i uu____26 =
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_1721(s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
  core_core_arch_x86___m256i uu____27 =
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_01(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  core_core_arch_x86___m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(core_core_arch_x86___m256i[5U]));
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_9b(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  core_core_arch_x86___m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(core_core_arch_x86___m256i[5U]));
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_09(
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_07(
    libcrux_sha3_generic_keccak_KeccakState_29 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_71(s);
    libcrux_sha3_generic_keccak_pi_01(s);
    libcrux_sha3_generic_keccak_chi_9b(s);
    libcrux_sha3_generic_keccak_iota_09(s, i0);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_37(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice blocks[4U]) {
  core_core_arch_x86___m256i(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[4U];
  memcpy(uu____1, blocks, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_avx2_load_block_ef_6a(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_07(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_91(
    core_core_arch_x86___m256i (*s)[5U], uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[2U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[3U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_avx2_load_block_c7(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full_ef
with const generics
- BLOCKSIZE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_05(
    core_core_arch_x86___m256i (*a)[5U], uint8_t b[4U][200U]) {
  core_core_arch_x86___m256i(*uu____0)[5U] = a;
  uint8_t uu____1[4U][200U];
  memcpy(uu____1, b, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_91(uu____0, uu____1);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_5e(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice last[4U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  core_core_arch_x86___m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_ef_05(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_07(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_e9(
    core_core_arch_x86___m256i (*s)[5U], Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i v0l =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32,
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v1h =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32,
            s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v2l =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49,
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v3h =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49,
            s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v0 =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    core_core_arch_x86___m256i v1 =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    core_core_arch_x86___m256i v2 =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    core_core_arch_x86___m256i v3 =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t, Eurydice_slice),
      s[i0][j0]);
  Eurydice_slice uu____0 = Eurydice_slice_subslice2(
      out[0U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____1 = Eurydice_slice_subslice2(
      out[1U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____1,
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____2 = Eurydice_slice_subslice2(
      out[2U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_slice_subslice2(
      out[3U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____4 =
        Eurydice_slice_subslice2(out[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____4,
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____5 =
        Eurydice_slice_subslice2(out[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____5,
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____6 =
        Eurydice_slice_subslice2(out[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____6,
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____7 =
        Eurydice_slice_subslice2(out[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____7,
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_full
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_0b(
    core_core_arch_x86___m256i (*s)[5U], uint8_t ret[4U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  uint8_t out2[200U] = {0U};
  uint8_t out3[200U] = {0U};
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out2, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out3, uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_avx2_store_block_e9(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____2[200U];
  memcpy(uu____2, out2, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____3[200U];
  memcpy(uu____3, out3, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[2U], uu____2, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[3U], uu____3, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_full_ef
with const generics
- BLOCKSIZE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_ef_99(
    core_core_arch_x86___m256i (*a)[5U], uint8_t ret[4U][200U]) {
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
libcrux_sha3_generic_keccak_squeeze_first_and_last_a4(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  uint8_t b[4U][200U];
  libcrux_sha3_simd_avx2_store_block_full_ef_99(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_ef
with const generics
- BLOCKSIZE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_f6(
    core_core_arch_x86___m256i (*a)[5U], Eurydice_slice b[4U]) {
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_e9(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_simd_avx2_store_block_ef_f6(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1c(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_07(s);
  libcrux_sha3_simd_avx2_store_block_ef_f6(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_77(
    libcrux_sha3_generic_keccak_KeccakState_29 s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_07(&s);
  uint8_t b[4U][200U];
  libcrux_sha3_simd_avx2_store_block_full_ef_99(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i0], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_14(
    Eurydice_slice data[4U], Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_KeccakState_29 s =
      libcrux_sha3_generic_keccak_new_1e_16();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_29 *uu____0 = &s;
    Eurydice_slice uu____1[4U];
    memcpy(uu____1, data, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice ret[4U];
    libcrux_sha3_simd_avx2_slice_n_ef(uu____1, i0 * (size_t)136U, (size_t)136U,
                                      ret);
    libcrux_sha3_generic_keccak_absorb_block_37(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_29 *uu____2 = &s;
  Eurydice_slice uu____3[4U];
  memcpy(uu____3, data, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret[4U];
  libcrux_sha3_simd_avx2_slice_n_ef(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_5e(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_a4(&s, out);
  } else {
    Eurydice_slice_uint8_t_4size_t__x2 uu____4 =
        libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)136U);
    Eurydice_slice o0[4U];
    memcpy(o0, uu____4.fst, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice o1[4U];
    memcpy(o1, uu____4.snd, (size_t)4U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_e9(&s, o0);
    core_ops_range_Range_b3 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_b3){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_b3, core_ops_range_Range_b3);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option_b3)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_4size_t__x2 uu____5 =
            libcrux_sha3_simd_avx2_split_at_mut_n_ef(o1, (size_t)136U);
        Eurydice_slice o[4U];
        memcpy(o, uu____5.fst, (size_t)4U * sizeof(Eurydice_slice));
        Eurydice_slice orest[4U];
        memcpy(orest, uu____5.snd, (size_t)4U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_1c(&s, o);
        memcpy(o1, orest, (size_t)4U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_77(s, o1);
    }
  }
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_avx2_x4_shake256(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf0[4U] = {input0, input1, input2, input3};
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_keccak_14(buf0, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_29
    libcrux_sha3_avx2_x4_incremental_KeccakState;

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_29
libcrux_sha3_avx2_x4_incremental_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_16();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_c70(
    core_core_arch_x86___m256i (*s)[5U], Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[0U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[1U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[2U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[3U], (size_t)32U * i0, (size_t)32U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_x86___m256i v0l =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v00, v10);
    core_core_arch_x86___m256i v1h =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v00, v10);
    core_core_arch_x86___m256i v2l =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v20, v30);
    core_core_arch_x86___m256i v3h =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v20, v30);
    core_core_arch_x86___m256i v0 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32, v0l, v2l, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v1 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32, v1h, v3h, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v2 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49, v0l, v2l, core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v3 =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49, v1h, v3h, core_core_arch_x86___m256i);
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
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      u8s, (size_t)0U, (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_slice_subslice2(blocks[0U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
      u8s, (size_t)8U, (size_t)16U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____1,
      Eurydice_slice_subslice2(blocks[1U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
      u8s, (size_t)16U, (size_t)24U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_slice_subslice2(blocks[2U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
      u8s, (size_t)24U, (size_t)32U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_slice_subslice2(blocks[3U], start, start + (size_t)8U, uint8_t,
                               Eurydice_slice),
      uint8_t, void *);
  core_core_arch_x86___m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N__23__as_slice((size_t)32U, u8s, uint8_t,
                                            Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = libcrux_intrinsics_avx2_mm256_xor_si256(s[i0][j0], u);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice uu____4 = Eurydice_array_to_subslice2(
        u8s0, (size_t)0U, (size_t)8U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____4,
        Eurydice_slice_subslice2(blocks[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____5 = Eurydice_array_to_subslice2(
        u8s0, (size_t)8U, (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____5,
        Eurydice_slice_subslice2(blocks[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____6 = Eurydice_array_to_subslice2(
        u8s0, (size_t)16U, (size_t)24U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____6,
        Eurydice_slice_subslice2(blocks[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____7 = Eurydice_array_to_subslice2(
        u8s0, (size_t)24U, (size_t)32U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____7,
        Eurydice_slice_subslice2(blocks[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice),
        uint8_t, void *);
    core_core_arch_x86___m256i u0 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
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
    core_core_arch_x86___m256i (*s)[5U], uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[2U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[3U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_avx2_load_block_c70(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full_ef
with const generics
- BLOCKSIZE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_050(
    core_core_arch_x86___m256i (*a)[5U], uint8_t b[4U][200U]) {
  core_core_arch_x86___m256i(*uu____0)[5U] = a;
  uint8_t uu____1[4U][200U];
  memcpy(uu____1, b, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_910(uu____0, uu____1);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_5e0(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice last[4U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)168U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  core_core_arch_x86___m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_avx2_load_block_full_ef_050(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_07(s);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_5e0(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_e90(
    core_core_arch_x86___m256i (*s)[5U], Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    core_core_arch_x86___m256i v0l =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32,
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v1h =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)32,
            s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v2l =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49,
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v3h =
        libcrux_intrinsics_avx2_mm256_permute2x128_si256(
            (int32_t)49,
            s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
            s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
             [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
            core_core_arch_x86___m256i);
    core_core_arch_x86___m256i v0 =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    core_core_arch_x86___m256i v1 =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    core_core_arch_x86___m256i v2 =
        libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    core_core_arch_x86___m256i v3 =
        libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t, Eurydice_slice),
      s[i0][j0]);
  Eurydice_slice uu____0 = Eurydice_slice_subslice2(
      out[0U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____0,
      Eurydice_array_to_subslice2(u8s, (size_t)0U, (size_t)8U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____1 = Eurydice_slice_subslice2(
      out[1U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____1,
      Eurydice_array_to_subslice2(u8s, (size_t)8U, (size_t)16U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____2 = Eurydice_slice_subslice2(
      out[2U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____2,
      Eurydice_array_to_subslice2(u8s, (size_t)16U, (size_t)24U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  Eurydice_slice uu____3 = Eurydice_slice_subslice2(
      out[3U], start, start + (size_t)8U, uint8_t, Eurydice_slice);
  core_slice___Slice_T___copy_from_slice(
      uu____3,
      Eurydice_array_to_subslice2(u8s, (size_t)24U, (size_t)32U, uint8_t,
                                  Eurydice_slice),
      uint8_t, void *);
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____4 =
        Eurydice_slice_subslice2(out[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____4,
        Eurydice_array_to_subslice2(u8s0, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____5 =
        Eurydice_slice_subslice2(out[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____5,
        Eurydice_array_to_subslice2(u8s0, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____6 =
        Eurydice_slice_subslice2(out[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____6,
        Eurydice_array_to_subslice2(u8s0, (size_t)16U, (size_t)24U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____7 =
        Eurydice_slice_subslice2(out[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____7,
        Eurydice_array_to_subslice2(u8s0, (size_t)24U, (size_t)32U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block_ef
with const generics
- BLOCKSIZE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_f60(
    core_core_arch_x86___m256i (*a)[5U], Eurydice_slice b[4U]) {
  libcrux_sha3_simd_avx2_store_block_e90(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_e90(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_simd_avx2_store_block_ef_f60(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1c0(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_07(s);
  libcrux_sha3_simd_avx2_store_block_ef_f60(s->st, out);
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
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_27(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_e90(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o2[4U];
  memcpy(o2, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o2);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_27(s, buf);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, buf);
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
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_e4(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_e90(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o20[4U];
  memcpy(o20, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o1);
  Eurydice_slice_uint8_t_4size_t__x2 uu____2 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o20, (size_t)168U);
  Eurydice_slice o2[4U];
  memcpy(o2, uu____2.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o30[4U];
  memcpy(o30, uu____2.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o2);
  Eurydice_slice_uint8_t_4size_t__x2 uu____3 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o30, (size_t)168U);
  Eurydice_slice o3[4U];
  memcpy(o3, uu____3.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o4[4U];
  memcpy(o4, uu____3.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_1c0(s, o4);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_e4(s, buf);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_5e(s, buf);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_block_e9(s, buf);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_29 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_1c(s, buf);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_avx2_H_DEFINED
#endif
