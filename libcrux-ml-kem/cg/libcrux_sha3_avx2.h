/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 166eab5075753a9e2d2f95b01c823557acc5c0fa
 */

#ifndef libcrux_sha3_avx2_H
#define libcrux_sha3_avx2_H

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_mlkem_core.h"
#include "libcrux_sha3_portable.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_zero_b0(void) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_xor5_b0(
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
  EURYDICE_ASSERT((int32_t)1 + (int32_t)63 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_and_not_xor_b0(__m256i a, __m256i b, __m256i c) {
  return libcrux_sha3_simd_avx2__vbcaxq_u64(a, b, c);
}

KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2__veorq_n_u64(__m256i a,
                                                                   uint64_t c) {
  __m256i c0 = libcrux_intrinsics_avx2_mm256_set1_epi64x((int64_t)c);
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, c0);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_constant_b0(__m256i a, uint64_t c) {
  return libcrux_sha3_simd_avx2__veorq_n_u64(a, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i libcrux_sha3_simd_avx2_xor_b0(__m256i a,
                                                             __m256i b) {
  return libcrux_intrinsics_avx2_mm256_xor_si256(a, b);
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
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_generic_keccak_new_80_a6(void) {
  libcrux_sha3_generic_keccak_KeccakState_55 lit;
  __m256i repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_sha3_simd_avx2_zero_b0();
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
static KRML_MUSTINLINE __m256i *libcrux_sha3_traits_get_ij_a6(__m256i *arr,
                                                              size_t i,
                                                              size_t j) {
  return &arr[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_5b(
    __m256i *state, Eurydice_slice *blocks, size_t offset) {
  Eurydice_slice_len(blocks[0U], uint8_t);
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[0U], start, start + (size_t)32U, uint8_t *));
    __m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[1U], start, start + (size_t)32U, uint8_t *));
    __m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[2U], start, start + (size_t)32U, uint8_t *));
    __m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[3U], start, start + (size_t)32U, uint8_t *));
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
            libcrux_sha3_traits_get_ij_a6(state, i0, j0)[0U], v0));
    libcrux_sha3_traits_set_ij_a6(
        state, i1, j1,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i1, j1)[0U], v1));
    libcrux_sha3_traits_set_ij_a6(
        state, i2, j2,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i2, j2)[0U], v2));
    libcrux_sha3_traits_set_ij_a6(
        state, i3, j3,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i3, j3)[0U], v3));
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)0U, (size_t)8U, uint8_t *),
      Eurydice_slice_subslice3(blocks[0U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)16U, uint8_t *),
      Eurydice_slice_subslice3(blocks[1U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)24U, uint8_t *),
      Eurydice_slice_subslice3(blocks[2U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)32U, uint8_t *),
      Eurydice_slice_subslice3(blocks[3U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  __m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N___as_slice((size_t)32U, u8s, uint8_t,
                                         Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  libcrux_sha3_traits_set_ij_a6(
      state, i0, j0,
      libcrux_intrinsics_avx2_mm256_xor_si256(
          libcrux_sha3_traits_get_ij_a6(state, i0, j0)[0U], u));
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)0U, (size_t)8U, uint8_t *),
        Eurydice_slice_subslice3(blocks[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)8U, (size_t)16U, uint8_t *),
        Eurydice_slice_subslice3(blocks[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)16U, (size_t)24U, uint8_t *),
        Eurydice_slice_subslice3(blocks[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)24U, (size_t)32U, uint8_t *),
        Eurydice_slice_subslice3(blocks[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    __m256i u0 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        core_array___Array_T__N___as_slice((size_t)32U, u8s0, uint8_t,
                                           Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_sha3_traits_set_ij_a6(
        state, i, j,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i, j)[0U], u0));
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_last_ad(
    __m256i *state, Eurydice_slice *blocks, size_t start, size_t len) {
  uint8_t buffers[4U][136U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(buffers[i0], (size_t)0U, len, uint8_t *),
        Eurydice_slice_subslice3(blocks[i0], start, start + len, uint8_t *),
        uint8_t);
    buffers[i0][len] = 31U;
    size_t uu____0 = i0;
    size_t uu____1 = (size_t)136U - (size_t)1U;
    buffers[uu____0][uu____1] = (uint32_t)buffers[uu____0][uu____1] | 128U;
  }
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)136U, buffers[0U], uint8_t),
      Eurydice_array_to_slice((size_t)136U, buffers[1U], uint8_t),
      Eurydice_array_to_slice((size_t)136U, buffers[2U], uint8_t),
      Eurydice_array_to_slice((size_t)136U, buffers[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_5b(state, buf, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<4usize> for
libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last_8f
with const generics
- RATE= 136
- DELIMITER= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_simd_avx2_load_last_8f_ad(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_avx2_load_last_ad(self->st, input, start, len);
}

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for
libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline __m256i *libcrux_sha3_generic_keccak_index_c2_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t_x2 index) {
  return libcrux_sha3_traits_get_ij_a6(self->st, index.fst, index.snd);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, __m256i ret[5U]) {
  __m256i c[5U] = {libcrux_sha3_simd_avx2_xor5_b0(
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)0U, (size_t)0U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)1U, (size_t)0U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)2U, (size_t)0U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)3U, (size_t)0U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)4U, (size_t)0U}))[0U]),
                   libcrux_sha3_simd_avx2_xor5_b0(
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)0U, (size_t)1U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)1U, (size_t)1U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)2U, (size_t)1U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)3U, (size_t)1U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)4U, (size_t)1U}))[0U]),
                   libcrux_sha3_simd_avx2_xor5_b0(
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)0U, (size_t)2U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)1U, (size_t)2U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)2U, (size_t)2U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)3U, (size_t)2U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)4U, (size_t)2U}))[0U]),
                   libcrux_sha3_simd_avx2_xor5_b0(
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)0U, (size_t)3U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)1U, (size_t)3U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)2U, (size_t)3U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)3U, (size_t)3U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)4U, (size_t)3U}))[0U]),
                   libcrux_sha3_simd_avx2_xor5_b0(
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)0U, (size_t)4U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)1U, (size_t)4U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)2U, (size_t)4U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)3U, (size_t)4U}))[0U],
                       libcrux_sha3_generic_keccak_index_c2_a6(
                           self, (size_t_x2{(size_t)4U, (size_t)4U}))[0U])};
  __m256i uu____0 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(
      c[((size_t)0U + (size_t)4U) % (size_t)5U],
      c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  __m256i uu____1 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(
      c[((size_t)1U + (size_t)4U) % (size_t)5U],
      c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  __m256i uu____2 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(
      c[((size_t)2U + (size_t)4U) % (size_t)5U],
      c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  __m256i uu____3 = libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(
      c[((size_t)3U + (size_t)4U) % (size_t)5U],
      c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  ret[0U] = uu____0;
  ret[1U] = uu____1;
  ret[2U] = uu____2;
  ret[3U] = uu____3;
  ret[4U] = libcrux_sha3_simd_avx2_rotate_left1_and_xor_b0(
      c[((size_t)4U + (size_t)4U) % (size_t)5U],
      c[((size_t)4U + (size_t)1U) % (size_t)5U]);
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
  EURYDICE_ASSERT((int32_t)36 + (int32_t)28 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_02(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)3 + (int32_t)61 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_ac(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)41 + (int32_t)23 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_020(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)18 + (int32_t)46 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_a9(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_76(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)44 + (int32_t)20 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_58(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)10 + (int32_t)54 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_e0(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)45 + (int32_t)19 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_63(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)2 + (int32_t)62 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_6a(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)62 + (int32_t)2 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_ab(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)6 + (int32_t)58 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_5b(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)43 + (int32_t)21 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_6f(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)15 + (int32_t)49 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_62(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)61 + (int32_t)3 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_23(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)28 + (int32_t)36 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_37(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)55 + (int32_t)9 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_bb(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)25 + (int32_t)39 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_b9(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)21 + (int32_t)43 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_54(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)56 + (int32_t)8 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_4c(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)27 + (int32_t)37 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_ce(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)20 + (int32_t)44 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_77(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)39 + (int32_t)25 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_25(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)8 + (int32_t)56 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_af(__m256i a, __m256i b) {
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
  EURYDICE_ASSERT((int32_t)14 + (int32_t)50 == (int32_t)64, "panic!");
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE __m256i
libcrux_sha3_simd_avx2_xor_and_rotate_b0_fd(__m256i a, __m256i b) {
  return libcrux_sha3_simd_avx2__vxarq_u64_fd(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.rho_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_rho_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, __m256i t[5U]) {
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_b0(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____0, (size_t)1U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_02(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)1U, (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____1 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____1, (size_t)2U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_ac(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)2U, (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____2 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____2, (size_t)3U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_020(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)3U, (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____3 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____3, (size_t)4U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_a9(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)4U, (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____4 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____4, (size_t)0U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_76(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____5 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____5, (size_t)1U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_58(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)1U, (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____6 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____6, (size_t)2U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_e0(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)2U, (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____7 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____7, (size_t)3U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_63(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)3U, (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____8 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____8, (size_t)4U, (size_t)1U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_6a(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)4U, (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____9 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____9, (size_t)0U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_ab(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____10 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____10, (size_t)1U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_5b(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)1U, (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____11 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____11, (size_t)2U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_6f(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)2U, (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____12 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____12, (size_t)3U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_62(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)3U, (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____13 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____13, (size_t)4U, (size_t)2U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_23(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)4U, (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____14 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____14, (size_t)0U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_37(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____15 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____15, (size_t)1U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_bb(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)1U, (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____16 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____16, (size_t)2U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_b9(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)2U, (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____17 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____17, (size_t)3U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_54(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)3U, (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____18 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____18, (size_t)4U, (size_t)3U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_4c(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)4U, (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____19 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____19, (size_t)0U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_ce(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____20 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____20, (size_t)1U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_77(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)1U, (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____21 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____21, (size_t)2U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_25(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)2U, (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____22 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____22, (size_t)3U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_af(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)3U, (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____23 = self;
  libcrux_sha3_generic_keccak_set_80_a6(
      uu____23, (size_t)4U, (size_t)4U,
      libcrux_sha3_simd_avx2_xor_and_rotate_b0_fd(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)4U, (size_t)4U}))[0U],
          t[4U]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self) {
  libcrux_sha3_generic_keccak_KeccakState_55 old = self[0U];
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)1U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)0U, (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)2U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)0U, (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)3U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)0U, (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)4U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)0U, (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)1U, (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)1U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)1U, (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)2U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)1U, (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)3U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)1U, (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)4U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)1U, (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)2U, (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)1U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)2U, (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)2U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)2U, (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)3U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)2U, (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)4U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)2U, (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)3U, (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)1U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)3U, (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)2U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)3U, (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)3U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)3U, (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)4U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)3U, (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)4U, (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)1U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)4U, (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)2U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)4U, (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)3U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)4U, (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)4U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_a6(
          &old, (size_t_x2{(size_t)4U, (size_t)1U}))[0U]);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self) {
  libcrux_sha3_generic_keccak_KeccakState_55 old = self[0U];
  core_ops_range_Range_08 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (core_ops_range_Range_08{(size_t)0U, (size_t)5U}),
          core_ops_range_Range_08, size_t, core_ops_range_Range_08);
  while (true) {
    Option_08 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, Option_08);
    if (uu____0.tag == None) {
      return;
    } else {
      size_t i0 = uu____0.f0;
      for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
        size_t j = i;
        libcrux_sha3_generic_keccak_set_80_a6(
            self, i0, j,
            libcrux_sha3_simd_avx2_and_not_xor_b0(
                libcrux_sha3_generic_keccak_index_c2_a6(self,
                                                        (size_t_x2{i0, j}))[0U],
                libcrux_sha3_generic_keccak_index_c2_a6(
                    &old, (size_t_x2{i0, (j + (size_t)2U) % (size_t)5U}))[0U],
                libcrux_sha3_generic_keccak_index_c2_a6(
                    &old, (size_t_x2{i0, (j + (size_t)1U) % (size_t)5U}))[0U]));
      }
      continue;
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "panic!");
    KRML_HOST_EXIT(255U);
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t i) {
  libcrux_sha3_generic_keccak_set_80_a6(
      self, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_avx2_xor_constant_b0(
          libcrux_sha3_generic_keccak_index_c2_a6(
              self, (size_t_x2{(size_t)0U, (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_constants_ROUNDCONSTANTS[i]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    __m256i t[5U];
    libcrux_sha3_generic_keccak_theta_80_a6(self, t);
    libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = self;
    __m256i uu____1[5U];
    memcpy(uu____1, t, (size_t)5U * sizeof(__m256i));
    libcrux_sha3_generic_keccak_rho_80_a6(uu____0, uu____1);
    libcrux_sha3_generic_keccak_pi_80_a6(self);
    libcrux_sha3_generic_keccak_chi_80_a6(self);
    libcrux_sha3_generic_keccak_iota_80_a6(self, i0);
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_fb(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  EURYDICE_ASSERT(!!((size_t)4U > (size_t)0U), "assert failure");
  EURYDICE_ASSERT(len < (size_t)136U, "panic!");
  libcrux_sha3_simd_avx2_load_last_8f_ad(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_5b(
    __m256i *s, Eurydice_slice out0, Eurydice_slice out1, Eurydice_slice out2,
    Eurydice_slice out3, size_t start, size_t len) {
  size_t chunks = len / (size_t)32U;
  core_ops_range_Range_08 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (core_ops_range_Range_08{(size_t)0U, chunks}),
          core_ops_range_Range_08, size_t, core_ops_range_Range_08);
  while (true) {
    Option_08 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, Option_08);
    if (uu____0.tag == None) {
      size_t rem = len % (size_t)32U;
      if (rem > (size_t)0U) {
        size_t start0 = start + (size_t)32U * chunks;
        uint8_t u8s[32U] = {0U};
        size_t chunks8 = rem / (size_t)8U;
        for (size_t i0 = (size_t)0U; i0 < chunks8; i0++) {
          size_t k = i0;
          size_t i = ((size_t)4U * chunks + k) / (size_t)5U;
          size_t j = ((size_t)4U * chunks + k) % (size_t)5U;
          libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
              Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
              libcrux_sha3_traits_get_ij_a6(s, i, j)[0U]);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out0, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)0U, (size_t)8U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out1, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)16U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out2, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)24U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out3, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)32U,
                                          uint8_t *),
              uint8_t);
        }
        size_t rem8 = rem % (size_t)8U;
        if (rem8 > (size_t)0U) {
          size_t i = ((size_t)4U * chunks + chunks8) / (size_t)5U;
          size_t j = ((size_t)4U * chunks + chunks8) % (size_t)5U;
          libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
              Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
              libcrux_sha3_traits_get_ij_a6(s, i, j)[0U]);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out0, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)0U, rem, uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out1, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)8U + rem,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out2, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)16U + rem,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out3, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)24U + rem,
                                          uint8_t *),
              uint8_t);
        }
      }
      return;
    } else {
      size_t i = uu____0.f0;
      size_t i0 = (size_t)4U * i / (size_t)5U;
      size_t j0 = (size_t)4U * i % (size_t)5U;
      size_t i1 = ((size_t)4U * i + (size_t)1U) / (size_t)5U;
      size_t j1 = ((size_t)4U * i + (size_t)1U) % (size_t)5U;
      size_t i2 = ((size_t)4U * i + (size_t)2U) / (size_t)5U;
      size_t j2 = ((size_t)4U * i + (size_t)2U) % (size_t)5U;
      size_t i3 = ((size_t)4U * i + (size_t)3U) / (size_t)5U;
      size_t j3 = ((size_t)4U * i + (size_t)3U) % (size_t)5U;
      __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i0, j0)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i2, j2)[0U], __m256i);
      __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i1, j1)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i3, j3)[0U], __m256i);
      __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i0, j0)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i2, j2)[0U], __m256i);
      __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i1, j1)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i3, j3)[0U], __m256i);
      __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
      __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
      __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
      __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out0, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v0);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out1, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v1);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out2, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v2);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out3, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v3);
      continue;
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "panic!");
    KRML_HOST_EXIT(255U);
  }
}

/**
This function found in impl
{libcrux_sha3::traits::Squeeze4<core::core_arch::x86::__m256i> for
libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.squeeze4_17
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_simd_avx2_squeeze4_17_5b(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3, size_t start,
    size_t len) {
  libcrux_sha3_simd_avx2_store_block_5b(self->st, out0, out1, out2, out3, start,
                                        len);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<4usize> for
libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_8f
with const generics
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_simd_avx2_load_block_8f_5b(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_avx2_load_block_5b(self->st, input, start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_avx2_load_block_8f_5b(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd256.keccak4
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_generic_keccak_simd256_keccak4_ad(
    Eurydice_slice *data, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  size_t uu____0 = Eurydice_slice_len(out0, uint8_t);
  if (uu____0 == Eurydice_slice_len(out1, uint8_t)) {
    size_t uu____1 = Eurydice_slice_len(out0, uint8_t);
    if (uu____1 == Eurydice_slice_len(out2, uint8_t)) {
      size_t uu____2 = Eurydice_slice_len(out0, uint8_t);
      if (uu____2 == Eurydice_slice_len(out3, uint8_t)) {
      }
    }
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
  size_t uu____3 = Eurydice_slice_len(data[0U], uint8_t);
  if (uu____3 == Eurydice_slice_len(data[1U], uint8_t)) {
    size_t uu____4 = Eurydice_slice_len(data[0U], uint8_t);
    if (uu____4 == Eurydice_slice_len(data[2U], uint8_t)) {
      size_t uu____5 = Eurydice_slice_len(data[0U], uint8_t);
      if (uu____5 == Eurydice_slice_len(data[3U], uint8_t)) {
      }
    }
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
  libcrux_sha3_generic_keccak_KeccakState_55 s =
      libcrux_sha3_generic_keccak_new_80_a6();
  size_t data_len = Eurydice_slice_len(data[0U], uint8_t);
  core_ops_range_Range_08 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (core_ops_range_Range_08{(size_t)0U, data_len / (size_t)136U}),
          core_ops_range_Range_08, size_t, core_ops_range_Range_08);
  while (true) {
    Option_08 uu____6 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, Option_08);
    if (uu____6.tag == None) {
      size_t rem = data_len % (size_t)136U;
      libcrux_sha3_generic_keccak_absorb_final_80_fb(&s, data, data_len - rem,
                                                     rem);
      size_t outlen = Eurydice_slice_len(out0, uint8_t);
      size_t blocks = outlen / (size_t)136U;
      size_t last = outlen - outlen % (size_t)136U;
      if (blocks == (size_t)0U) {
        libcrux_sha3_simd_avx2_squeeze4_17_5b(&s, out0, out1, out2, out3,
                                              (size_t)0U, outlen);
        return;
      } else {
        libcrux_sha3_simd_avx2_squeeze4_17_5b(&s, out0, out1, out2, out3,
                                              (size_t)0U, (size_t)136U);
        for (size_t i = (size_t)1U; i < blocks; i++) {
          size_t i0 = i;
          libcrux_sha3_generic_keccak_keccakf1600_80_a6(&s);
          libcrux_sha3_simd_avx2_squeeze4_17_5b(
              &s, out0, out1, out2, out3, i0 * (size_t)136U, (size_t)136U);
        }
        if (last < outlen) {
          libcrux_sha3_generic_keccak_keccakf1600_80_a6(&s);
          libcrux_sha3_simd_avx2_squeeze4_17_5b(&s, out0, out1, out2, out3,
                                                last, outlen - last);
        }
        return;
      }
    } else {
      size_t i = uu____6.f0;
      libcrux_sha3_generic_keccak_absorb_block_80_97(&s, data,
                                                     i * (size_t)136U);
      continue;
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "panic!");
    KRML_HOST_EXIT(255U);
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
  Eurydice_slice buf[4U] = {input0, input1, input2, input3};
  libcrux_sha3_generic_keccak_simd256_keccak4_ad(buf, out0, out1, out2, out3);
}

typedef libcrux_sha3_generic_keccak_KeccakState_55
    libcrux_sha3_avx2_x4_incremental_KeccakState;

/**
 Initialise the [`KeccakState`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_avx2_x4_incremental_init(void) {
  return libcrux_sha3_generic_keccak_new_80_a6();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_block_3a(
    __m256i *state, Eurydice_slice *blocks, size_t offset) {
  Eurydice_slice_len(blocks[0U], uint8_t);
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[0U], start, start + (size_t)32U, uint8_t *));
    __m256i v10 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[1U], start, start + (size_t)32U, uint8_t *));
    __m256i v20 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[2U], start, start + (size_t)32U, uint8_t *));
    __m256i v30 =
        libcrux_intrinsics_avx2_mm256_loadu_si256_u8(Eurydice_slice_subslice3(
            blocks[3U], start, start + (size_t)32U, uint8_t *));
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
            libcrux_sha3_traits_get_ij_a6(state, i0, j0)[0U], v0));
    libcrux_sha3_traits_set_ij_a6(
        state, i1, j1,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i1, j1)[0U], v1));
    libcrux_sha3_traits_set_ij_a6(
        state, i2, j2,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i2, j2)[0U], v2));
    libcrux_sha3_traits_set_ij_a6(
        state, i3, j3,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i3, j3)[0U], v3));
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)0U, (size_t)8U, uint8_t *),
      Eurydice_slice_subslice3(blocks[0U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)16U, uint8_t *),
      Eurydice_slice_subslice3(blocks[1U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)24U, uint8_t *),
      Eurydice_slice_subslice3(blocks[2U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)32U, uint8_t *),
      Eurydice_slice_subslice3(blocks[3U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  __m256i u = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
      core_array___Array_T__N___as_slice((size_t)32U, u8s, uint8_t,
                                         Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  libcrux_sha3_traits_set_ij_a6(
      state, i0, j0,
      libcrux_intrinsics_avx2_mm256_xor_si256(
          libcrux_sha3_traits_get_ij_a6(state, i0, j0)[0U], u));
  if (rem == (size_t)16U) {
    uint8_t u8s0[32U] = {0U};
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)0U, (size_t)8U, uint8_t *),
        Eurydice_slice_subslice3(blocks[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)8U, (size_t)16U, uint8_t *),
        Eurydice_slice_subslice3(blocks[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)16U, (size_t)24U, uint8_t *),
        Eurydice_slice_subslice3(blocks[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(u8s0, (size_t)24U, (size_t)32U, uint8_t *),
        Eurydice_slice_subslice3(blocks[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    __m256i u0 = libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
        core_array___Array_T__N___as_slice((size_t)32U, u8s0, uint8_t,
                                           Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    libcrux_sha3_traits_set_ij_a6(
        state, i, j,
        libcrux_intrinsics_avx2_mm256_xor_si256(
            libcrux_sha3_traits_get_ij_a6(state, i, j)[0U], u0));
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_load_last_c6(
    __m256i *state, Eurydice_slice *blocks, size_t start, size_t len) {
  uint8_t buffers[4U][168U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(buffers[i0], (size_t)0U, len, uint8_t *),
        Eurydice_slice_subslice3(blocks[i0], start, start + len, uint8_t *),
        uint8_t);
    buffers[i0][len] = 31U;
    size_t uu____0 = i0;
    size_t uu____1 = (size_t)168U - (size_t)1U;
    buffers[uu____0][uu____1] = (uint32_t)buffers[uu____0][uu____1] | 128U;
  }
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)168U, buffers[0U], uint8_t),
      Eurydice_array_to_slice((size_t)168U, buffers[1U], uint8_t),
      Eurydice_array_to_slice((size_t)168U, buffers[2U], uint8_t),
      Eurydice_array_to_slice((size_t)168U, buffers[3U], uint8_t)};
  libcrux_sha3_simd_avx2_load_block_3a(state, buf, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<4usize> for
libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last_8f
with const generics
- RATE= 168
- DELIMITER= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_simd_avx2_load_last_8f_c6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_avx2_load_last_c6(self->st, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
- DELIM= 31
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_fb0(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  EURYDICE_ASSERT(!!((size_t)4U > (size_t)0U), "assert failure");
  EURYDICE_ASSERT(len < (size_t)168U, "panic!");
  libcrux_sha3_simd_avx2_load_last_8f_c6(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
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
  libcrux_sha3_generic_keccak_absorb_final_80_fb0(
      uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void libcrux_sha3_simd_avx2_store_block_3a(
    __m256i *s, Eurydice_slice out0, Eurydice_slice out1, Eurydice_slice out2,
    Eurydice_slice out3, size_t start, size_t len) {
  size_t chunks = len / (size_t)32U;
  core_ops_range_Range_08 iter =
      core_iter_traits_collect__core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__into_iter(
          (core_ops_range_Range_08{(size_t)0U, chunks}),
          core_ops_range_Range_08, size_t, core_ops_range_Range_08);
  while (true) {
    Option_08 uu____0 =
        core_iter_range__core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___next(
            &iter, size_t, Option_08);
    if (uu____0.tag == None) {
      size_t rem = len % (size_t)32U;
      if (rem > (size_t)0U) {
        size_t start0 = start + (size_t)32U * chunks;
        uint8_t u8s[32U] = {0U};
        size_t chunks8 = rem / (size_t)8U;
        for (size_t i0 = (size_t)0U; i0 < chunks8; i0++) {
          size_t k = i0;
          size_t i = ((size_t)4U * chunks + k) / (size_t)5U;
          size_t j = ((size_t)4U * chunks + k) % (size_t)5U;
          libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
              Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
              libcrux_sha3_traits_get_ij_a6(s, i, j)[0U]);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out0, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)0U, (size_t)8U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out1, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)16U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out2, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)24U,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out3, start0 + (size_t)8U * k,
                                       start0 + (size_t)8U * (k + (size_t)1U),
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)32U,
                                          uint8_t *),
              uint8_t);
        }
        size_t rem8 = rem % (size_t)8U;
        if (rem8 > (size_t)0U) {
          size_t i = ((size_t)4U * chunks + chunks8) / (size_t)5U;
          size_t j = ((size_t)4U * chunks + chunks8) % (size_t)5U;
          libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
              Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
              libcrux_sha3_traits_get_ij_a6(s, i, j)[0U]);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out0, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)0U, rem, uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out1, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)8U, (size_t)8U + rem,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out2, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)16U, (size_t)16U + rem,
                                          uint8_t *),
              uint8_t);
          Eurydice_slice_copy(
              Eurydice_slice_subslice3(out3, start0 + len - rem8, start0 + len,
                                       uint8_t *),
              Eurydice_array_to_subslice3(u8s, (size_t)24U, (size_t)24U + rem,
                                          uint8_t *),
              uint8_t);
        }
      }
      return;
    } else {
      size_t i = uu____0.f0;
      size_t i0 = (size_t)4U * i / (size_t)5U;
      size_t j0 = (size_t)4U * i % (size_t)5U;
      size_t i1 = ((size_t)4U * i + (size_t)1U) / (size_t)5U;
      size_t j1 = ((size_t)4U * i + (size_t)1U) % (size_t)5U;
      size_t i2 = ((size_t)4U * i + (size_t)2U) / (size_t)5U;
      size_t j2 = ((size_t)4U * i + (size_t)2U) % (size_t)5U;
      size_t i3 = ((size_t)4U * i + (size_t)3U) / (size_t)5U;
      size_t j3 = ((size_t)4U * i + (size_t)3U) % (size_t)5U;
      __m256i v0l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i0, j0)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i2, j2)[0U], __m256i);
      __m256i v1h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)32, libcrux_sha3_traits_get_ij_a6(s, i1, j1)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i3, j3)[0U], __m256i);
      __m256i v2l = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i0, j0)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i2, j2)[0U], __m256i);
      __m256i v3h = libcrux_intrinsics_avx2_mm256_permute2x128_si256(
          (int32_t)49, libcrux_sha3_traits_get_ij_a6(s, i1, j1)[0U],
          libcrux_sha3_traits_get_ij_a6(s, i3, j3)[0U], __m256i);
      __m256i v0 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v0l, v1h);
      __m256i v1 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v0l, v1h);
      __m256i v2 = libcrux_intrinsics_avx2_mm256_unpacklo_epi64(v2l, v3h);
      __m256i v3 = libcrux_intrinsics_avx2_mm256_unpackhi_epi64(v2l, v3h);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out0, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v0);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out1, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v1);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out2, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v2);
      libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
          Eurydice_slice_subslice3(out3, start + (size_t)32U * i,
                                   start + (size_t)32U * (i + (size_t)1U),
                                   uint8_t *),
          v3);
      continue;
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "panic!");
    KRML_HOST_EXIT(255U);
  }
}

/**
This function found in impl
{libcrux_sha3::traits::Squeeze4<core::core_arch::x86::__m256i> for
libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.squeeze4_17
with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_sha3_simd_avx2_squeeze4_17_3a(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3, size_t start,
    size_t len) {
  libcrux_sha3_simd_avx2_store_block_3a(self->st, out0, out1, out2, out3, start,
                                        len);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.simd256.squeeze_first_three_blocks_81 with const
generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_simd256_squeeze_first_three_blocks_81_3a(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  libcrux_sha3_simd_avx2_squeeze4_17_3a(self, out0, out1, out2, out3,
                                        (size_t)0U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
  libcrux_sha3_simd_avx2_squeeze4_17_3a(self, out0, out1, out2, out3,
                                        (size_t)168U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
  libcrux_sha3_simd_avx2_squeeze4_17_3a(
      self, out0, out1, out2, out3, (size_t)2U * (size_t)168U, (size_t)168U);
}

/**
 Squeeze three blocks
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  libcrux_sha3_generic_keccak_simd256_squeeze_first_three_blocks_81_3a(
      s, out0, out1, out2, out3);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::KeccakState<core::core_arch::x86::__m256i,
4usize>[core::marker::Sized<core::core_arch::x86::__m256i>,
libcrux_sha3::simd::avx2::{libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.simd256.squeeze_next_block_81 with const generics
- RATE= 168
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_simd256_squeeze_next_block_81_3a(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3,
    size_t start) {
  libcrux_sha3_generic_keccak_keccakf1600_80_a6(self);
  libcrux_sha3_simd_avx2_squeeze4_17_3a(self, out0, out1, out2, out3, start,
                                        (size_t)168U);
}

/**
 Squeeze another block
*/
KRML_ATTRIBUTE_TARGET("avx2")
static KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  libcrux_sha3_generic_keccak_simd256_squeeze_next_block_81_3a(
      s, out0, out1, out2, out3, (size_t)0U);
}

#define libcrux_sha3_avx2_H_DEFINED
#endif /* libcrux_sha3_avx2_H */
