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
 * Libcrux: 75cbe9ea0e459cf8a62d97e8a867411e0dd8529a
 */

#ifndef __libcrux_sha3_avx2_H
#define __libcrux_sha3_avx2_H

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_mlkem_core.h"
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
libcrux_sha3_simd_avx2_rotate_left_76(__m256i x) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      libcrux_intrinsics_avx2_mm256_slli_epi64((int32_t)1, x, __m256i),
      libcrux_intrinsics_avx2_mm256_srli_epi64((int32_t)63, x, __m256i));
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vrax1q_u64(__m256i a,
                                                                  __m256i b) {
  __m256i uu____0 = a;
  return libcrux_intrinsics_avx2_mm256_xor_si256(
      uu____0, libcrux_sha3_simd_avx2_rotate_left_76(b));
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
typedef struct libcrux_sha3_generic_keccak_KeccakState_55_s {
  __m256i st[25U];
} libcrux_sha3_generic_keccak_KeccakState_55;

/**
 Create a new Shake128 x4 state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_89
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_generic_keccak_new_89_a6(void) {
  libcrux_sha3_generic_keccak_KeccakState_55 lit;
  __m256i repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_sha3_simd_avx2_zero_ef();
  }
  memcpy(lit.st, repeat_expression, (size_t)25U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_traits_set_ij_a6(__m256i *arr,
                                                          size_t i, size_t j,
                                                          __m256i value) {
  arr[(size_t)5U * j + i] = value;
}

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_traits_get_ij_a6(__m256i *arr,
                                                             size_t i,
                                                             size_t j) {
  return arr[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_5b(
    __m256i *state, Eurydice_slice *blocks, size_t offset) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[0U], start, start + (size_t)32U, uint8_t));
    __m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[1U], start, start + (size_t)32U, uint8_t));
    __m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[2U], start, start + (size_t)32U, uint8_t));
    __m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[3U], start, start + (size_t)32U, uint8_t));
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
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    libcrux_sha3_traits_set_ij_a6(
        state, i0, j0,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i0, j0), v0));
    libcrux_sha3_traits_set_ij_a6(
        state, i1, j1,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i1, j1), v1));
    libcrux_sha3_traits_set_ij_a6(
        state, i2, j2,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i2, j2), v2));
    libcrux_sha3_traits_set_ij_a6(
        state, i3, j3,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i3, j3), v3));
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)136U / (size_t)32U);
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
  libcrux_sha3_traits_set_ij_a6(
      state, i0, j0,
      libcrux_intrinsics_avx2_mm256_xor_si256(
          libcrux_sha3_traits_get_ij_a6(state, i0, j0), u));
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
    libcrux_sha3_traits_set_ij_a6(
        state, i, j,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i, j), u0));
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_ef_5b(
    __m256i *state, Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_simd_avx2_load_block_5b(state, blocks, start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.get_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i libcrux_sha3_generic_keccak_get_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t i, size_t j) {
  return libcrux_sha3_traits_get_ij_a6(self->st, i, j);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.set_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_generic_keccak_set_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t i, size_t j,
    __m256i v) {
  libcrux_sha3_traits_set_ij_a6(self->st, i, j, v);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_02(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_02(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_02(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_02(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_ac(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_ac(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_ac(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_ac(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_020(__m256i x) {
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
libcrux_sha3_simd_avx2__vxarq_u64_020(__m256i a, __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_020(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_020(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_a9(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_a9(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_a9(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_a9(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_76(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_76(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_76(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_58(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_58(__m256i a,
                                                                    __m256i b) {
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
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_ef_58(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_e0(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_e0(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_e0(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_e0(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_63(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_63(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_63(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_63(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_6a(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_6a(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_6a(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_6a(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_ab(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_ab(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_ab(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_ab(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_5b(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_5b(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_5b(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_5b(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_6f(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_6f(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_6f(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_6f(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_62(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_62(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_62(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_62(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_23(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_23(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_23(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_23(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_37(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_37(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_37(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_37(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_bb(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_bb(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_bb(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_bb(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_b9(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_b9(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_b9(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_b9(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_54(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_54(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_54(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_54(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_4c(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_4c(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_4c(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_4c(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_ce(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_ce(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_ce(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_ce(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_77(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_77(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_77(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_77(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_25(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_25(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_25(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_25(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_af(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_af(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_af(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_af(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left_fd(__m256i x) {
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
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__vxarq_u64_fd(__m256i a,
                                                                    __m256i b) {
  __m256i ab = libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
  return libcrux_sha3_simd_avx2_rotate_left_fd(ab);
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
libcrux_sha3_simd_avx2_xor_and_rotate_ef_fd(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_fd(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  __m256i c[5U] = {
      libcrux_sha3_simd_avx2_xor5_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)0U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)0U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)0U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)0U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)0U)),
      libcrux_sha3_simd_avx2_xor5_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)1U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)1U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)1U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)1U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)1U)),
      libcrux_sha3_simd_avx2_xor5_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)2U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)2U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)2U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)2U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)2U)),
      libcrux_sha3_simd_avx2_xor5_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)3U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)3U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)3U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)3U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)3U)),
      libcrux_sha3_simd_avx2_xor5_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)4U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)4U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)4U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)4U),
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)4U))};
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
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)0U),
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____4 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____4, (size_t)1U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_02(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)0U),
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____5 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____5, (size_t)2U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_ac(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)0U),
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____6 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____6, (size_t)3U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_020(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)0U),
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____7 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____7, (size_t)4U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_a9(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)0U),
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____8 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____8, (size_t)0U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_76(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)1U),
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____9 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____9, (size_t)1U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_58(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)1U),
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____10 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____10, (size_t)2U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_e0(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)1U),
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____11 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____11, (size_t)3U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_63(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)1U),
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____12 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____12, (size_t)4U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_6a(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)1U),
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____13 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____13, (size_t)0U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_ab(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)2U),
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____14 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____14, (size_t)1U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_5b(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)2U),
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____15 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____15, (size_t)2U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_6f(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)2U),
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____16 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____16, (size_t)3U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_62(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)2U),
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____17 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____17, (size_t)4U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_23(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)2U),
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____18 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____18, (size_t)0U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_37(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)3U),
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____19 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____19, (size_t)1U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_bb(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)3U),
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____20 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____20, (size_t)2U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_b9(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)3U),
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____21 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____21, (size_t)3U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_54(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)3U),
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____22 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____22, (size_t)4U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_4c(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)3U),
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____23 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____23, (size_t)0U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_ce(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)4U),
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____24 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____24, (size_t)1U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_77(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)1U, (size_t)4U),
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____25 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____25, (size_t)2U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_25(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)2U, (size_t)4U),
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____26 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____26, (size_t)3U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_af(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)3U, (size_t)4U),
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____27 = s;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____27, (size_t)4U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_ef_fd(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)4U, (size_t)4U),
          t[4U]));
}

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0,
TraitClause@2])#3}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.clone_db
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_generic_keccak_clone_db_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self) {
  libcrux_sha3_generic_keccak_KeccakState_55 lit;
  __m256i ret[25U];
  core_array___core__clone__Clone_for__Array_T__N___20__clone(
      (size_t)25U, self->st, ret, __m256i, void *);
  memcpy(lit.st, ret, (size_t)25U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  libcrux_sha3_generic_keccak_KeccakState_55 old =
      libcrux_sha3_generic_keccak_clone_db_a6(s);
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)1U, (size_t)0U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)0U, (size_t)3U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)2U, (size_t)0U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)0U, (size_t)1U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)3U, (size_t)0U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)0U, (size_t)4U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)4U, (size_t)0U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)0U, (size_t)2U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)1U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)1U, (size_t)1U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)1U, (size_t)1U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)1U, (size_t)4U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)2U, (size_t)1U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)1U, (size_t)2U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)3U, (size_t)1U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)1U, (size_t)0U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)4U, (size_t)1U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)1U, (size_t)3U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)2U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)2U, (size_t)2U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)1U, (size_t)2U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)2U, (size_t)0U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)2U, (size_t)2U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)2U, (size_t)3U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)3U, (size_t)2U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)2U, (size_t)1U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)4U, (size_t)2U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)2U, (size_t)4U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)3U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)3U, (size_t)3U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)1U, (size_t)3U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)3U, (size_t)1U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)2U, (size_t)3U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)3U, (size_t)4U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)3U, (size_t)3U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)3U, (size_t)2U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)4U, (size_t)3U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)3U, (size_t)0U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)4U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)4U, (size_t)4U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)1U, (size_t)4U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)4U, (size_t)2U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)2U, (size_t)4U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)4U, (size_t)0U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)3U, (size_t)4U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)4U, (size_t)3U));
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)4U, (size_t)4U,
      libcrux_sha3_generic_keccak_get_80_a6(&old, (size_t)4U, (size_t)1U));
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  libcrux_sha3_generic_keccak_KeccakState_55 old =
      libcrux_sha3_generic_keccak_clone_db_a6(s);
  for (size_t i0 = (size_t)0U; i0 < (size_t)5U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t j = i;
      libcrux_sha3_generic_keccak_set_80_a6(
          s, i1, j,
          libcrux_sha3_simd_avx2_and_not_xor_ef(
              libcrux_sha3_generic_keccak_get_80_a6(s, i1, j),
              libcrux_sha3_generic_keccak_get_80_a6(
                  &old, i1, (j + (size_t)2U) % (size_t)5U),
              libcrux_sha3_generic_keccak_get_80_a6(
                  &old, i1, (j + (size_t)1U) % (size_t)5U)));
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, size_t i) {
  libcrux_sha3_generic_keccak_set_80_a6(
      s, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_constant_ef(
          libcrux_sha3_generic_keccak_get_80_a6(s, (size_t)0U, (size_t)0U),
          libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]));
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_a6(s);
    libcrux_sha3_generic_keccak_pi_a6(s);
    libcrux_sha3_generic_keccak_chi_a6(s);
    libcrux_sha3_generic_keccak_iota_a6(s, i0);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_avx2_load_block_ef_5b(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_a6(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_5b(
    __m256i *state, uint8_t (*blocks)[200U], size_t start) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_5b(state, buf, start);
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_5b(
    __m256i *state, uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_simd_avx2_load_block_full_5b(state, blocks, start);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fb(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i0], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i0], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i0][len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_simd_avx2_load_block_full_ef_5b(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_a6(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_5b(
    __m256i *s, Eurydice_slice *out) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i0, j0),
        libcrux_sha3_traits_get_ij_a6(s, i2, j2), __m256i);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i1, j1),
        libcrux_sha3_traits_get_ij_a6(s, i3, j3), __m256i);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i0, j0),
        libcrux_sha3_traits_get_ij_a6(s, i2, j2), __m256i);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i1, j1),
        libcrux_sha3_traits_get_ij_a6(s, i3, j3), __m256i);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
      libcrux_sha3_traits_get_ij_a6(s, i0, j0));
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
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t),
        libcrux_sha3_traits_get_ij_a6(s, i, j));
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_5b(
    __m256i *state, uint8_t (*out)[200U]) {
  Eurydice_slice_uint8_t_200size_t__x2 uu____0 = Eurydice_slice_split_at_mut(
      Eurydice_array_to_slice((size_t)4U, out, uint8_t[200U]), (size_t)1U,
      uint8_t[200U], Eurydice_slice_uint8_t_200size_t__x2);
  Eurydice_slice out0 = uu____0.fst;
  Eurydice_slice rest0 = uu____0.snd;
  Eurydice_slice_uint8_t_200size_t__x2 uu____1 = Eurydice_slice_split_at_mut(
      rest0, (size_t)1U, uint8_t[200U], Eurydice_slice_uint8_t_200size_t__x2);
  Eurydice_slice out1 = uu____1.fst;
  Eurydice_slice rest = uu____1.snd;
  Eurydice_slice_uint8_t_200size_t__x2 uu____2 = Eurydice_slice_split_at_mut(
      rest, (size_t)1U, uint8_t[200U], Eurydice_slice_uint8_t_200size_t__x2);
  Eurydice_slice out2 = uu____2.fst;
  Eurydice_slice out3 = uu____2.snd;
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice(
          (size_t)200U,
          Eurydice_slice_index(out0, (size_t)0U, uint8_t[200U],
                               uint8_t(*)[200U]),
          uint8_t),
      Eurydice_array_to_slice(
          (size_t)200U,
          Eurydice_slice_index(out1, (size_t)0U, uint8_t[200U],
                               uint8_t(*)[200U]),
          uint8_t),
      Eurydice_array_to_slice(
          (size_t)200U,
          Eurydice_slice_index(out2, (size_t)0U, uint8_t[200U],
                               uint8_t(*)[200U]),
          uint8_t),
      Eurydice_array_to_slice(
          (size_t)200U,
          Eurydice_slice_index(out3, (size_t)0U, uint8_t[200U],
                               uint8_t(*)[200U]),
          uint8_t)};
  libcrux_sha3_simd_avx2_store_block_5b(state, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_full_ef_5b(
    __m256i *state, uint8_t (*out)[200U]) {
  libcrux_sha3_simd_avx2_store_block_full_5b(state, out);
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
libcrux_sha3_generic_keccak_squeeze_first_and_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  uint8_t b[4U][200U] = {{0U}};
  libcrux_sha3_simd_avx2_store_block_full_ef_5b(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_5b(
    __m256i *a, Eurydice_slice *b) {
  libcrux_sha3_simd_avx2_store_block_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out) {
  libcrux_sha3_simd_avx2_store_block_ef_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out) {
  libcrux_sha3_generic_keccak_keccakf1600_a6(s);
  libcrux_sha3_simd_avx2_store_block_ef_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 s, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_keccakf1600_a6(&s);
  uint8_t b[4U][200U] = {{0U}};
  libcrux_sha3_simd_avx2_store_block_full_ef_5b(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_fb(
    Eurydice_slice *data, Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_KeccakState_55 s =
      libcrux_sha3_generic_keccak_new_89_a6();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_97(&s, data, i0 * (size_t)136U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_fb(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_97(&s, out);
  } else {
    Eurydice_slice_uint8_t_4size_t__x2 uu____2 =
        libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)136U);
    Eurydice_slice o0[4U];
    memcpy(o0, uu____2.fst, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice o1[4U];
    memcpy(o1, uu____2.snd, (size_t)4U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_97(&s, o0);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      Eurydice_slice_uint8_t_4size_t__x2 uu____3 =
          libcrux_sha3_simd_avx2_split_at_mut_n_ef(o1, (size_t)136U);
      Eurydice_slice o[4U];
      memcpy(o, uu____3.fst, (size_t)4U * sizeof(Eurydice_slice));
      Eurydice_slice orest[4U];
      memcpy(orest, uu____3.snd, (size_t)4U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_squeeze_next_block_97(&s, o);
      memcpy(o1, orest, (size_t)4U * sizeof(Eurydice_slice));
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_97(s, o1);
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
  libcrux_sha3_generic_keccak_keccak_fb(buf0, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_55
    libcrux_sha3_avx2_x4_incremental_KeccakState;

/**
 Initialise the [`KeccakState`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_avx2_x4_incremental_init(void) {
  return libcrux_sha3_generic_keccak_new_89_a6();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_3a(
    __m256i *state, Eurydice_slice *blocks, size_t offset) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[0U], start, start + (size_t)32U, uint8_t));
    __m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[1U], start, start + (size_t)32U, uint8_t));
    __m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[2U], start, start + (size_t)32U, uint8_t));
    __m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice2(
            blocks[3U], start, start + (size_t)32U, uint8_t));
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
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    libcrux_sha3_traits_set_ij_a6(
        state, i0, j0,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i0, j0), v0));
    libcrux_sha3_traits_set_ij_a6(
        state, i1, j1,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i1, j1), v1));
    libcrux_sha3_traits_set_ij_a6(
        state, i2, j2,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i2, j2), v2));
    libcrux_sha3_traits_set_ij_a6(
        state, i3, j3,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i3, j3), v3));
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)168U / (size_t)32U);
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
  libcrux_sha3_traits_set_ij_a6(
      state, i0, j0,
      libcrux_intrinsics_avx2_mm256_xor_si256(
          libcrux_sha3_traits_get_ij_a6(state, i0, j0), u));
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
    libcrux_sha3_traits_set_ij_a6(
        state, i, j,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i, j), u0));
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_3a(
    __m256i *state, uint8_t (*blocks)[200U], size_t start) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_3a(state, buf, start);
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_full_ef_3a(
    __m256i *state, uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_simd_avx2_load_block_full_3a(state, blocks, start);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fb0(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[4U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i0], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i0], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i0][len] = 31U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)168U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_simd_avx2_load_block_full_ef_3a(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_a6(s);
}

/**
 Absorb
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = s;
  Eurydice_slice uu____1[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_fb0(
      uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_3a(
    __m256i *s, Eurydice_slice *out) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i0, j0),
        libcrux_sha3_traits_get_ij_a6(s, i2, j2), __m256i);
    __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i1, j1),
        libcrux_sha3_traits_get_ij_a6(s, i3, j3), __m256i);
    __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i0, j0),
        libcrux_sha3_traits_get_ij_a6(s, i2, j2), __m256i);
    __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
        (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i1, j1),
        libcrux_sha3_traits_get_ij_a6(s, i3, j3), __m256i);
    __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v0);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v1);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v2);
    libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i4,
                                 (size_t)32U * (i4 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
      Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
      libcrux_sha3_traits_get_ij_a6(s, i0, j0));
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
        Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t),
        libcrux_sha3_traits_get_ij_a6(s, i, j));
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
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_ef_3a(
    __m256i *a, Eurydice_slice *b) {
  libcrux_sha3_simd_avx2_store_block_3a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out) {
  libcrux_sha3_simd_avx2_store_block_ef_3a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out) {
  libcrux_sha3_generic_keccak_keccakf1600_a6(s);
  libcrux_sha3_simd_avx2_store_block_ef_3a(s->st, out);
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
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_970(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o2[4U];
  memcpy(o2, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o2);
}

/**
 Squeeze three blocks
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_97(s, buf);
}

/**
 Squeeze another block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, buf);
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
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_970(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o20[4U];
  memcpy(o20, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o1);
  Eurydice_slice_uint8_t_4size_t__x2 uu____2 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o20, (size_t)168U);
  Eurydice_slice o2[4U];
  memcpy(o2, uu____2.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o30[4U];
  memcpy(o30, uu____2.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o2);
  Eurydice_slice_uint8_t_4size_t__x2 uu____3 =
      libcrux_sha3_simd_avx2_split_at_mut_n_ef(o30, (size_t)168U);
  Eurydice_slice o3[4U];
  memcpy(o3, uu____3.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o4[4U];
  memcpy(o4, uu____3.snd, (size_t)4U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_970(s, o4);
}

/**
 Squeeze five blocks
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_97(s, buf);
}

/**
 Absorb
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = s;
  Eurydice_slice uu____1[4U] = {data0, data1, data2, data3};
  libcrux_sha3_generic_keccak_absorb_final_fb(
      uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
 Squeeze block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_first_block_97(s, buf);
}

/**
 Squeeze next block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  libcrux_sha3_generic_keccak_squeeze_next_block_97(s, buf);
}

#define __libcrux_sha3_avx2_H_DEFINED
#endif
