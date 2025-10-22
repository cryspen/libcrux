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

#ifndef libcrux_sha3_portable_H
#define libcrux_sha3_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_mlkem_core.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_zero_d2(void) {
  return 0ULL;
}

static KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__veor5q_u64(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  return (((a ^ b) ^ c) ^ d) ^ e;
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_xor5_d2(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  return libcrux_sha3_simd_portable__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_76(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)1);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vrax1q_u64(uint64_t a, uint64_t b) {
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_simd_portable_rotate_left_76(b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vrax1q_u64(a, b);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vbcaxq_u64(uint64_t a, uint64_t b, uint64_t c) {
  return a ^ (b & ~c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_and_not_xor_d2(uint64_t a, uint64_t b, uint64_t c) {
  return libcrux_sha3_simd_portable__vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__veorq_n_u64(uint64_t a, uint64_t c) {
  return a ^ c;
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_constant_d2(uint64_t a, uint64_t c) {
  return libcrux_sha3_simd_portable__veorq_n_u64(a, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_xor_d2(uint64_t a,
                                                                  uint64_t b) {
  return a ^ b;
}

static const uint64_t
    libcrux_sha3_generic_keccak_constants_ROUNDCONSTANTS[24U] = {
        1ULL,
        32898ULL,
        9223372036854808714ULL,
        9223372039002292224ULL,
        32907ULL,
        2147483649ULL,
        9223372039002292353ULL,
        9223372036854808585ULL,
        138ULL,
        136ULL,
        2147516425ULL,
        2147483658ULL,
        2147516555ULL,
        9223372036854775947ULL,
        9223372036854808713ULL,
        9223372036854808579ULL,
        9223372036854808578ULL,
        9223372036854775936ULL,
        32778ULL,
        9223372039002259466ULL,
        9223372039002292353ULL,
        9223372036854808704ULL,
        2147483649ULL,
        9223372039002292232ULL};

typedef struct size_t_x2_s {
  size_t fst;
  size_t snd;
} size_t_x2;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types uint64_t
with const generics
- $1size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_17_s {
  uint64_t st[25U];
} libcrux_sha3_generic_keccak_KeccakState_17;

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_generic_keccak_new_80_04(void) {
  libcrux_sha3_generic_keccak_KeccakState_17 lit;
  uint64_t repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = libcrux_sha3_simd_portable_zero_d2();
  }
  memcpy(lit.st, repeat_expression, (size_t)25U * sizeof(uint64_t));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE uint64_t *libcrux_sha3_traits_get_ij_04(uint64_t *arr,
                                                               size_t i,
                                                               size_t j) {
  return &arr[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_traits_set_ij_04(uint64_t *arr,
                                                          size_t i, size_t j,
                                                          uint64_t value) {
  arr[(size_t)5U * j + i] = value;
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_block_f8(
    uint64_t *state, Eurydice_slice blocks, size_t start) {
  uint64_t state_flat[25U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U,
                                 uint8_t *),
        Eurydice_slice, uint8_t[8U], TryFromSliceError);
    unwrap_26_68(dst, uu____0);
    state_flat[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U,
                                      i0 % (size_t)5U)[0U] ^
            state_flat[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 72
*/
static inline void libcrux_sha3_simd_portable_load_block_a1_f8(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_f8(self->st, input[0U], start);
}

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for
libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types uint64_t
with const generics
- N= 1
*/
static inline uint64_t *libcrux_sha3_generic_keccak_index_c2_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t_x2 index) {
  return libcrux_sha3_traits_get_ij_04(self->st, index.fst, index.snd);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, uint64_t ret[5U]) {
  uint64_t c[5U] = {
      libcrux_sha3_simd_portable_xor5_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)0U}))[0U]),
      libcrux_sha3_simd_portable_xor5_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)1U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)1U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)1U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)1U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)1U}))[0U]),
      libcrux_sha3_simd_portable_xor5_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)2U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)2U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)2U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)2U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)2U}))[0U]),
      libcrux_sha3_simd_portable_xor5_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)3U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)3U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)3U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)3U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)3U}))[0U]),
      libcrux_sha3_simd_portable_xor5_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)4U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)4U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)4U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)4U}))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)4U}))[0U])};
  uint64_t uu____0 = libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(
      c[((size_t)0U + (size_t)4U) % (size_t)5U],
      c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____1 = libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(
      c[((size_t)1U + (size_t)4U) % (size_t)5U],
      c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____2 = libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(
      c[((size_t)2U + (size_t)4U) % (size_t)5U],
      c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____3 = libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(
      c[((size_t)3U + (size_t)4U) % (size_t)5U],
      c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  ret[0U] = uu____0;
  ret[1U] = uu____1;
  ret[2U] = uu____2;
  ret[3U] = uu____3;
  ret[4U] = libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(
      c[((size_t)4U + (size_t)4U) % (size_t)5U],
      c[((size_t)4U + (size_t)1U) % (size_t)5U]);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.set_80
with types uint64_t
with const generics
- N= 1
*/
static inline void libcrux_sha3_generic_keccak_set_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t i, size_t j,
    uint64_t v) {
  libcrux_sha3_traits_set_ij_04(self->st, i, j, v);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_02(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)36);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_02(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_02(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_02(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_ac(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)3);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_ac(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_ac(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_020(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)41);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_020(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_020(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_020(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_a9(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)18);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_a9(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_a9(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_76(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_76(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_76(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_58(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)44);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_58(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_58(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_58(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_e0(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)10);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_e0(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_e0(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_63(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)45);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_63(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_63(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_63(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_6a(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)2);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_6a(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_6a(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_ab(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)62);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_ab(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_ab(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_5b(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)6);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_5b(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_5b(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_6f(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)43);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_6f(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_6f(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_62(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)15);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_62(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_62(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_62(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_23(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)61);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_23(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_23(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_23(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_37(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)28);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_37(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_37(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_37(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_bb(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)55);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_bb(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_bb(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_b9(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)25);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_b9(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_b9(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_54(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)21);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_54(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_54(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_54(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_4c(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)56);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_4c(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_4c(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_ce(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)27);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_ce(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_ce(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_77(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)20);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_77(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_77(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_77(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_25(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)39);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_25(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_25(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_25(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_af(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)8);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_af(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_af(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_af(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left_fd(uint64_t x) {
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)14);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vxarq_u64_fd(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable_rotate_left_fd(a ^ b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(uint64_t a, uint64_t b) {
  return libcrux_sha3_simd_portable__vxarq_u64_fd(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.rho_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_rho_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, uint64_t t[5U]) {
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____0, (size_t)1U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_02(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____1 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____1, (size_t)2U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____2, (size_t)3U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_020(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____3 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____3, (size_t)4U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)0U}))[0U],
          t[0U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____4 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____4, (size_t)0U, (size_t)1U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_76(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____5 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____5, (size_t)1U, (size_t)1U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_58(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____6 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____6, (size_t)2U, (size_t)1U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____7 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____7, (size_t)3U, (size_t)1U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_63(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____8 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____8, (size_t)4U, (size_t)1U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)1U}))[0U],
          t[1U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____9 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____9, (size_t)0U, (size_t)2U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____10 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____10, (size_t)1U, (size_t)2U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____11 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____11, (size_t)2U, (size_t)2U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____12 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____12, (size_t)3U, (size_t)2U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_62(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____13 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____13, (size_t)4U, (size_t)2U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_23(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)2U}))[0U],
          t[2U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____14 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____14, (size_t)0U, (size_t)3U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_37(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____15 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____15, (size_t)1U, (size_t)3U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____16 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____16, (size_t)2U, (size_t)3U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____17 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____17, (size_t)3U, (size_t)3U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_54(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____18 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____18, (size_t)4U, (size_t)3U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)3U}))[0U],
          t[3U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____19 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____19, (size_t)0U, (size_t)4U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____20 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____20, (size_t)1U, (size_t)4U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_77(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                              .snd = (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____21 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____21, (size_t)2U, (size_t)4U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_25(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                              .snd = (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____22 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____22, (size_t)3U, (size_t)4U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_af(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                              .snd = (size_t)4U}))[0U],
          t[4U]));
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____23 = self;
  libcrux_sha3_generic_keccak_set_80_04(
      uu____23, (size_t)4U, (size_t)4U,
      libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                              .snd = (size_t)4U}))[0U],
          t[4U]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  libcrux_sha3_generic_keccak_KeccakState_17 old = self[0U];
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)1U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                          .snd = (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)2U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                          .snd = (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)3U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                          .snd = (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)4U, (size_t)0U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                          .snd = (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                          .snd = (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)1U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                          .snd = (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)2U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                          .snd = (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)3U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                          .snd = (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)4U, (size_t)1U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                          .snd = (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                          .snd = (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)1U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                          .snd = (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)2U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                          .snd = (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)3U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                          .snd = (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)4U, (size_t)2U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                          .snd = (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                          .snd = (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)1U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                          .snd = (size_t)1U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)2U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                          .snd = (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)3U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                          .snd = (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)4U, (size_t)3U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                          .snd = (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                          .snd = (size_t)4U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)1U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                          .snd = (size_t)2U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)2U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                          .snd = (size_t)0U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)3U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                          .snd = (size_t)3U}))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)4U, (size_t)4U,
      libcrux_sha3_generic_keccak_index_c2_04(
          &old, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                          .snd = (size_t)1U}))[0U]);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  libcrux_sha3_generic_keccak_KeccakState_17 old = self[0U];
  for (size_t i0 = (size_t)0U; i0 < (size_t)5U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t j = i;
      libcrux_sha3_generic_keccak_set_80_04(
          self, i1, j,
          libcrux_sha3_simd_portable_and_not_xor_d2(
              libcrux_sha3_generic_keccak_index_c2_04(
                  self, (KRML_CLITERAL(size_t_x2){.fst = i1, .snd = j}))[0U],
              libcrux_sha3_generic_keccak_index_c2_04(
                  &old,
                  (KRML_CLITERAL(size_t_x2){
                      .fst = i1, .snd = (j + (size_t)2U) % (size_t)5U}))[0U],
              libcrux_sha3_generic_keccak_index_c2_04(
                  &old,
                  (KRML_CLITERAL(size_t_x2){
                      .fst = i1, .snd = (j + (size_t)1U) % (size_t)5U}))[0U]));
    }
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t i) {
  libcrux_sha3_generic_keccak_set_80_04(
      self, (size_t)0U, (size_t)0U,
      libcrux_sha3_simd_portable_xor_constant_d2(
          libcrux_sha3_generic_keccak_index_c2_04(
              self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                              .snd = (size_t)0U}))[0U],
          libcrux_sha3_generic_keccak_constants_ROUNDCONSTANTS[i]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    uint64_t t[5U];
    libcrux_sha3_generic_keccak_theta_80_04(self, t);
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = self;
    uint64_t uu____1[5U];
    memcpy(uu____1, t, (size_t)5U * sizeof(uint64_t));
    libcrux_sha3_generic_keccak_rho_80_04(uu____0, uu____1);
    libcrux_sha3_generic_keccak_pi_80_04(self);
    libcrux_sha3_generic_keccak_chi_80_04(self);
    libcrux_sha3_generic_keccak_iota_80_04(self, i0);
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_a1_f8(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 72
- DELIMITER= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_96(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[72U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 6U;
  size_t uu____0 = (size_t)72U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_f8(
      state, Eurydice_array_to_slice((size_t)72U, buffer, uint8_t), (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 72
- DELIMITER= 6
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_96(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_96(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_96(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_store_block_f8(
    uint64_t *s, Eurydice_slice out, size_t start, size_t len) {
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, start + (size_t)8U * i0, start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, i0 / (size_t)5U, i0 % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice3(
        out, start + len - remaining, start + len, uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, octets / (size_t)5U,
                                      octets % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice3(ret, (size_t)0U, remaining, uint8_t *),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 72
*/
static inline void libcrux_sha3_simd_portable_squeeze_13_f8(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_store_block_f8(self->st, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 72
- DELIM= 6
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_96(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)72U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c6(&s, buf, i0 * (size_t)72U);
  }
  size_t rem = data_len % (size_t)72U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, (size_t)0U, (size_t)72U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, i0 * (size_t)72U,
                                               (size_t)72U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 512 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha512(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_96(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_block_5b(
    uint64_t *state, Eurydice_slice blocks, size_t start) {
  uint64_t state_flat[25U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U,
                                 uint8_t *),
        Eurydice_slice, uint8_t[8U], TryFromSliceError);
    unwrap_26_68(dst, uu____0);
    state_flat[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U,
                                      i0 % (size_t)5U)[0U] ^
            state_flat[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 136
*/
static inline void libcrux_sha3_simd_portable_load_block_a1_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_5b(self->st, input[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_a1_5b(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_ad(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[136U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 6U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_5b(
      state, Eurydice_array_to_slice((size_t)136U, buffer, uint8_t),
      (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 6
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_ad(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_ad(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e0(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_ad(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_store_block_5b(
    uint64_t *s, Eurydice_slice out, size_t start, size_t len) {
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, start + (size_t)8U * i0, start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, i0 / (size_t)5U, i0 % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice3(
        out, start + len - remaining, start + len, uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, octets / (size_t)5U,
                                      octets % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice3(ret, (size_t)0U, remaining, uint8_t *),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 136
*/
static inline void libcrux_sha3_simd_portable_squeeze_13_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_store_block_5b(self->st, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 6
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_ad(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c60(&s, buf, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e0(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, i0 * (size_t)136U,
                                               (size_t)136U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 256 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha256(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_ad(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_ad0(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[136U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 31U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_5b(
      state, Eurydice_array_to_slice((size_t)136U, buffer, uint8_t),
      (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 31
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_ad0(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_ad0(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e1(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_ad0(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 31
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_ad0(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c60(&s, buf, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e1(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, i0 * (size_t)136U,
                                               (size_t)136U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHAKE256 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_shake256(
    Eurydice_slice digest, Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_ad0(data, digest);
}

typedef libcrux_sha3_generic_keccak_KeccakState_17
    libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_80_04();
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_block_3a(
    uint64_t *state, Eurydice_slice blocks, size_t start) {
  uint64_t state_flat[25U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U,
                                 uint8_t *),
        Eurydice_slice, uint8_t[8U], TryFromSliceError);
    unwrap_26_68(dst, uu____0);
    state_flat[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U,
                                      i0 % (size_t)5U)[0U] ^
            state_flat[i0]);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_c6(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[168U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 31U;
  size_t uu____0 = (size_t)168U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_3a(
      state, Eurydice_array_to_slice((size_t)168U, buffer, uint8_t),
      (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 168
- DELIMITER= 31
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_c6(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e2(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_c6(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
 Absorb
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data0) {
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = s;
  Eurydice_slice uu____1[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_80_9e2(
      uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_store_block_3a(
    uint64_t *s, Eurydice_slice out, size_t start, size_t len) {
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, start + (size_t)8U * i0, start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, i0 / (size_t)5U, i0 % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice3(
        out, start + len - remaining, start + len, uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, octets / (size_t)5U,
                                      octets % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice3(ret, (size_t)0U, remaining, uint8_t *),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 168
*/
static inline void libcrux_sha3_simd_portable_squeeze_13_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_store_block_3a(self->st, out, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_three_blocks_b4 with const
generics
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out) {
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)0U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)168U,
                                           (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)2U * (size_t)168U,
                                           (size_t)168U);
}

/**
 Squeeze three blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(s,
                                                                        out0);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4 with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start) {
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, start, (size_t)168U);
}

/**
 Squeeze another block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(s, out0,
                                                                (size_t)0U);
}

#define libcrux_sha3_Algorithm_Sha224 1
#define libcrux_sha3_Algorithm_Sha256 2
#define libcrux_sha3_Algorithm_Sha384 3
#define libcrux_sha3_Algorithm_Sha512 4

typedef uint8_t libcrux_sha3_Algorithm;

typedef uint8_t libcrux_sha3_Sha3_224Digest[28U];

typedef uint8_t libcrux_sha3_Sha3_256Digest[32U];

typedef uint8_t libcrux_sha3_Sha3_384Digest[48U];

typedef uint8_t libcrux_sha3_Sha3_512Digest[64U];

/**
 Returns the output size of a digest.
*/
static inline size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode) {
  switch (mode) {
    case libcrux_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_sha3_Algorithm_Sha256: {
      return (size_t)32U;
    }
    case libcrux_sha3_Algorithm_Sha384: {
      return (size_t)48U;
    }
    case libcrux_sha3_Algorithm_Sha512: {
      return (size_t)64U;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (size_t)28U;
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_block_2c(
    uint64_t *state, Eurydice_slice blocks, size_t start) {
  uint64_t state_flat[25U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U,
                                 uint8_t *),
        Eurydice_slice, uint8_t[8U], TryFromSliceError);
    unwrap_26_68(dst, uu____0);
    state_flat[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U,
                                      i0 % (size_t)5U)[0U] ^
            state_flat[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 144
*/
static inline void libcrux_sha3_simd_portable_load_block_a1_2c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_2c(self->st, input[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_a1_2c(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 144
- DELIMITER= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_1e(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[144U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 6U;
  size_t uu____0 = (size_t)144U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_2c(
      state, Eurydice_array_to_slice((size_t)144U, buffer, uint8_t),
      (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 144
- DELIMITER= 6
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_1e(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_1e(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e3(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_1e(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_store_block_2c(
    uint64_t *s, Eurydice_slice out, size_t start, size_t len) {
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, start + (size_t)8U * i0, start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, i0 / (size_t)5U, i0 % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice3(
        out, start + len - remaining, start + len, uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, octets / (size_t)5U,
                                      octets % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice3(ret, (size_t)0U, remaining, uint8_t *),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 144
*/
static inline void libcrux_sha3_simd_portable_squeeze_13_2c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_store_block_2c(self->st, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 144
- DELIM= 6
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_1e(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)144U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c61(&s, buf, i0 * (size_t)144U);
  }
  size_t rem = data_len % (size_t)144U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e3(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, (size_t)0U, (size_t)144U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, i0 * (size_t)144U,
                                               (size_t)144U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 224 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_1e(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_block_7a(
    uint64_t *state, Eurydice_slice blocks, size_t start) {
  uint64_t state_flat[25U] = {0U};
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U,
                                 uint8_t *),
        Eurydice_slice, uint8_t[8U], TryFromSliceError);
    unwrap_26_68(dst, uu____0);
    state_flat[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(
        state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U,
                                      i0 % (size_t)5U)[0U] ^
            state_flat[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 104
*/
static inline void libcrux_sha3_simd_portable_load_block_a1_7a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_7a(self->st, input[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_a1_7a(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 104
- DELIMITER= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_load_last_7c(
    uint64_t *state, Eurydice_slice blocks, size_t start, size_t len) {
  uint8_t buffer[104U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(buffer, (size_t)0U, len, uint8_t *),
      Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *), uint8_t);
  buffer[len] = 6U;
  size_t uu____0 = (size_t)104U - (size_t)1U;
  buffer[uu____0] = (uint32_t)buffer[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_7a(
      state, Eurydice_array_to_slice((size_t)104U, buffer, uint8_t),
      (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 104
- DELIMITER= 6
*/
static inline void libcrux_sha3_simd_portable_load_last_a1_7c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_7c(self->st, input[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_80_9e4(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_load_last_a1_7c(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_portable_store_block_7a(
    uint64_t *s, Eurydice_slice out, size_t start, size_t len) {
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, start + (size_t)8U * i0, start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, i0 / (size_t)5U, i0 % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice3(
        out, start + len - remaining, start + len, uint8_t *);
    uint8_t ret[8U];
    core_num__u64__to_le_bytes(
        libcrux_sha3_traits_get_ij_04(s, octets / (size_t)5U,
                                      octets % (size_t)5U)[0U],
        ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice3(ret, (size_t)0U, remaining, uint8_t *),
        uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 104
*/
static inline void libcrux_sha3_simd_portable_squeeze_13_7a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len) {
  libcrux_sha3_simd_portable_store_block_7a(self->st, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 104
- DELIM= 6
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_7c(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)104U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c62(&s, buf, i0 * (size_t)104U);
  }
  size_t rem = data_len % (size_t)104U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e4(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, (size_t)0U, (size_t)104U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, i0 * (size_t)104U,
                                               (size_t)104U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 384 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_7c(data, digest);
}

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
static inline void libcrux_sha3_sha224_ema(Eurydice_slice digest,
                                           Eurydice_slice payload) {
  libcrux_sha3_portable_sha224(digest, payload);
}

/**
 SHA3 224
*/
static inline void libcrux_sha3_sha224(Eurydice_slice data, uint8_t ret[28U]) {
  uint8_t out[28U] = {0U};
  libcrux_sha3_sha224_ema(Eurydice_array_to_slice((size_t)28U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)28U * sizeof(uint8_t));
}

/**
 SHA3 256
*/
static inline void libcrux_sha3_sha256_ema(Eurydice_slice digest,
                                           Eurydice_slice payload) {
  libcrux_sha3_portable_sha256(digest, payload);
}

/**
 SHA3 256
*/
static inline void libcrux_sha3_sha256(Eurydice_slice data, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  libcrux_sha3_sha256_ema(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 SHA3 384
*/
static inline void libcrux_sha3_sha384_ema(Eurydice_slice digest,
                                           Eurydice_slice payload) {
  libcrux_sha3_portable_sha384(digest, payload);
}

/**
 SHA3 384
*/
static inline void libcrux_sha3_sha384(Eurydice_slice data, uint8_t ret[48U]) {
  uint8_t out[48U] = {0U};
  libcrux_sha3_sha384_ema(Eurydice_array_to_slice((size_t)48U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)48U * sizeof(uint8_t));
}

/**
 SHA3 512
*/
static inline void libcrux_sha3_sha512_ema(Eurydice_slice digest,
                                           Eurydice_slice payload) {
  libcrux_sha3_portable_sha512(digest, payload);
}

/**
 SHA3 512
*/
static inline void libcrux_sha3_sha512(Eurydice_slice data, uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  libcrux_sha3_sha512_ema(Eurydice_array_to_slice((size_t)64U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 168
*/
static inline void libcrux_sha3_simd_portable_load_block_a1_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_3a(self->st, input[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_80_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_simd_portable_load_block_a1_3a(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 168
- DELIM= 31
*/
static inline void libcrux_sha3_generic_keccak_portable_keccak1_c6(
    Eurydice_slice data, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)168U; i++) {
    size_t i0 = i;
    Eurydice_slice buf[1U] = {data};
    libcrux_sha3_generic_keccak_absorb_block_80_c63(&s, buf, i0 * (size_t)168U);
  }
  size_t rem = data_len % (size_t)168U;
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e2(&s, buf, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, (size_t)0U, outlen);
  } else {
    libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, (size_t)0U, (size_t)168U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, i0 * (size_t)168U,
                                               (size_t)168U);
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHAKE128 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_shake128(
    Eurydice_slice digest, Eurydice_slice data) {
  libcrux_sha3_generic_keccak_portable_keccak1_c6(data, digest);
}

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
static inline void libcrux_sha3_shake128_ema(Eurydice_slice out,
                                             Eurydice_slice data) {
  libcrux_sha3_portable_shake128(out, data);
}

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
static inline void libcrux_sha3_shake256_ema(Eurydice_slice out,
                                             Eurydice_slice data) {
  libcrux_sha3_portable_shake256(out, data);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_five_blocks_b4 with const
generics
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out) {
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)0U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)168U,
                                           (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)2U * (size_t)168U,
                                           (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)3U * (size_t)168U,
                                           (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)4U * (size_t)168U,
                                           (size_t)168U);
}

/**
 Squeeze five blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(s, out0);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data) {
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = s;
  Eurydice_slice uu____1[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_80_9e1(
      uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data, uint8_t));
}

/**
 Create a new SHAKE-256 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_80_04();
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_block_b4 with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out) {
  libcrux_sha3_simd_portable_squeeze_13_5b(self, out, (size_t)0U, (size_t)136U);
}

/**
 Squeeze the first SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(s, out);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4 with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start) {
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_5b(self, out, start, (size_t)136U);
}

/**
 Squeeze the next SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(s, out,
                                                                (size_t)0U);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_e2_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_xof_KeccakXofState_e2;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
    libcrux_sha3_portable_incremental_Shake256Xof;

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.fill_buffer_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_xof_fill_buffer_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)136U) {
      consumed = (size_t)136U - self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)136U, self->buf[i0], self->buf_len, uint8_t, size_t,
            uint8_t[]);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t,
                                       uint8_t[]),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_full_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_xof_absorb_full_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs) {
  size_t input_consumed =
      libcrux_sha3_generic_keccak_xof_fill_buffer_35_c6(self, inputs);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      uint8_t buf[136U] = {0U};
      borrowed[i] = core_array___Array_T__N___as_slice((size_t)136U, buf,
                                                       uint8_t, Eurydice_slice);
    }
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      borrowed[i0] =
          Eurydice_array_to_slice((size_t)136U, self->buf[i0], uint8_t);
    }
    libcrux_sha3_simd_portable_load_block_a1_5b(&self->inner, borrowed,
                                                (size_t)0U);
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    libcrux_sha3_simd_portable_load_block_a1_5b(
        &self->inner, inputs, input_consumed + i0 * (size_t)136U);
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
  }
  return remainder;
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_absorb_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs) {
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_xof_absorb_full_35_c6(self, inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice_copy(Eurydice_array_to_subslice3(
                              self->buf[i0], self->buf_len,
                              self->buf_len + input_remainder_len, uint8_t *),
                          Eurydice_slice_subslice_from(
                              inputs[i0], input_len - input_remainder_len,
                              uint8_t, size_t, uint8_t[]),
                          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
 Shake256 absorb
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
static inline void libcrux_sha3_portable_incremental_absorb_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_xof_absorb_35_c6(self, buf);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_final_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_absorb_final_35_9e(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs) {
  libcrux_sha3_generic_keccak_xof_absorb_35_c6(self, inputs);
  Eurydice_slice borrowed[1U];
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    uint8_t buf[136U] = {0U};
    borrowed[i] = core_array___Array_T__N___as_slice((size_t)136U, buf, uint8_t,
                                                     Eurydice_slice);
  }
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    borrowed[i0] =
        Eurydice_array_to_slice((size_t)136U, self->buf[i0], uint8_t);
  }
  libcrux_sha3_simd_portable_load_last_a1_ad0(&self->inner, borrowed,
                                              (size_t)0U, self->buf_len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
}

/**
 Shake256 absorb final
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
static inline void libcrux_sha3_portable_incremental_absorb_final_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_xof_absorb_final_35_9e(self, buf);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.zero_block_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline void libcrux_sha3_generic_keccak_xof_zero_block_35_c6(
    uint8_t ret[136U]) {
  memset(ret, 0U, 136U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.new_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
libcrux_sha3_generic_keccak_xof_new_35_c6(void) {
  libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_80_04();
  uint8_t repeat_expression[1U][136U];
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    libcrux_sha3_generic_keccak_xof_zero_block_35_c6(repeat_expression[i]);
  }
  memcpy(lit.buf, repeat_expression, (size_t)1U * sizeof(uint8_t[136U]));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
 Shake256 new state
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
static inline libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
libcrux_sha3_portable_incremental_new_42(void) {
  return libcrux_sha3_generic_keccak_xof_new_35_c6();
}

/**
 Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
*/
/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, 1usize,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.squeeze_85
with types uint64_t
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_squeeze_85_c7(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice out) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out, uint8_t);
  if (out_len > (size_t)0U) {
    if (out_len <= (size_t)136U) {
      libcrux_sha3_simd_portable_squeeze_13_5b(&self->inner, out, (size_t)0U,
                                               out_len);
    } else {
      size_t blocks = out_len / (size_t)136U;
      for (size_t i = (size_t)0U; i < blocks; i++) {
        size_t i0 = i;
        libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
        libcrux_sha3_simd_portable_squeeze_13_5b(
            &self->inner, out, i0 * (size_t)136U, (size_t)136U);
      }
      size_t remaining = out_len % (size_t)136U;
      if (remaining > (size_t)0U) {
        libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
        libcrux_sha3_simd_portable_squeeze_13_5b(
            &self->inner, out, blocks * (size_t)136U, remaining);
      }
    }
    self->sponge = true;
  }
}

/**
 Shake256 squeeze
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice out) {
  libcrux_sha3_generic_keccak_xof_squeeze_85_c7(self, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_97_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_xof_KeccakXofState_97;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_97
    libcrux_sha3_portable_incremental_Shake128Xof;

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.fill_buffer_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_xof_fill_buffer_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)168U) {
      consumed = (size_t)168U - self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)168U, self->buf[i0], self->buf_len, uint8_t, size_t,
            uint8_t[]);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t,
                                       uint8_t[]),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_full_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_xof_absorb_full_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs) {
  size_t input_consumed =
      libcrux_sha3_generic_keccak_xof_fill_buffer_35_c60(self, inputs);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      uint8_t buf[168U] = {0U};
      borrowed[i] = core_array___Array_T__N___as_slice((size_t)168U, buf,
                                                       uint8_t, Eurydice_slice);
    }
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      borrowed[i0] =
          Eurydice_array_to_slice((size_t)168U, self->buf[i0], uint8_t);
    }
    libcrux_sha3_simd_portable_load_block_a1_3a(&self->inner, borrowed,
                                                (size_t)0U);
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    libcrux_sha3_simd_portable_load_block_a1_3a(
        &self->inner, inputs, input_consumed + i0 * (size_t)168U);
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
  }
  return remainder;
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_absorb_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs) {
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_xof_absorb_full_35_c60(self, inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice_copy(Eurydice_array_to_subslice3(
                              self->buf[i0], self->buf_len,
                              self->buf_len + input_remainder_len, uint8_t *),
                          Eurydice_slice_subslice_from(
                              inputs[i0], input_len - input_remainder_len,
                              uint8_t, size_t, uint8_t[]),
                          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
static inline void libcrux_sha3_portable_incremental_absorb_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_xof_absorb_35_c60(self, buf);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_final_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_absorb_final_35_9e0(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs) {
  libcrux_sha3_generic_keccak_xof_absorb_35_c60(self, inputs);
  Eurydice_slice borrowed[1U];
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    uint8_t buf[168U] = {0U};
    borrowed[i] = core_array___Array_T__N___as_slice((size_t)168U, buf, uint8_t,
                                                     Eurydice_slice);
  }
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    borrowed[i0] =
        Eurydice_array_to_slice((size_t)168U, self->buf[i0], uint8_t);
  }
  libcrux_sha3_simd_portable_load_last_a1_c6(&self->inner, borrowed, (size_t)0U,
                                             self->buf_len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
}

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
static inline void libcrux_sha3_portable_incremental_absorb_final_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_xof_absorb_final_35_9e0(self, buf);
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.zero_block_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline void libcrux_sha3_generic_keccak_xof_zero_block_35_c60(
    uint8_t ret[168U]) {
  memset(ret, 0U, 168U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.new_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline libcrux_sha3_generic_keccak_xof_KeccakXofState_97
libcrux_sha3_generic_keccak_xof_new_35_c60(void) {
  libcrux_sha3_generic_keccak_xof_KeccakXofState_97 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_80_04();
  uint8_t repeat_expression[1U][168U];
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    libcrux_sha3_generic_keccak_xof_zero_block_35_c60(repeat_expression[i]);
  }
  memcpy(lit.buf, repeat_expression, (size_t)1U * sizeof(uint8_t[168U]));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
static inline libcrux_sha3_generic_keccak_xof_KeccakXofState_97
libcrux_sha3_portable_incremental_new_26(void) {
  return libcrux_sha3_generic_keccak_xof_new_35_c60();
}

/**
 Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
*/
/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, 1usize,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.squeeze_85
with types uint64_t
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_xof_squeeze_85_13(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice out) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out, uint8_t);
  if (out_len > (size_t)0U) {
    if (out_len <= (size_t)168U) {
      libcrux_sha3_simd_portable_squeeze_13_3a(&self->inner, out, (size_t)0U,
                                               out_len);
    } else {
      size_t blocks = out_len / (size_t)168U;
      for (size_t i = (size_t)0U; i < blocks; i++) {
        size_t i0 = i;
        libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
        libcrux_sha3_simd_portable_squeeze_13_3a(
            &self->inner, out, i0 * (size_t)168U, (size_t)168U);
      }
      size_t remaining = out_len % (size_t)168U;
      if (remaining > (size_t)0U) {
        libcrux_sha3_generic_keccak_keccakf1600_80_04(&self->inner);
        libcrux_sha3_simd_portable_squeeze_13_3a(
            &self->inner, out, blocks * (size_t)168U, remaining);
      }
    }
    self->sponge = true;
  }
}

/**
 Shake128 squeeze
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice out) {
  libcrux_sha3_generic_keccak_xof_squeeze_85_13(self, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_sha3::portable::KeccakState}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_clone_fe(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  return self[0U];
}

/**
This function found in impl {core::convert::From<libcrux_sha3::Algorithm> for
u32}
*/
static inline uint32_t libcrux_sha3_from_6c(libcrux_sha3_Algorithm v) {
  switch (v) {
    case libcrux_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_sha3_Algorithm_Sha256: {
      return 2U;
    }
    case libcrux_sha3_Algorithm_Sha384: {
      return 3U;
    }
    case libcrux_sha3_Algorithm_Sha512: {
      return 4U;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return 1U;
}

/**
This function found in impl {core::convert::From<u32> for
libcrux_sha3::Algorithm}
*/
static inline libcrux_sha3_Algorithm libcrux_sha3_from_29(uint32_t v) {
  switch (v) {
    case 1U: {
      break;
    }
    case 2U: {
      return libcrux_sha3_Algorithm_Sha256;
    }
    case 3U: {
      return libcrux_sha3_Algorithm_Sha384;
    }
    case 4U: {
      return libcrux_sha3_Algorithm_Sha512;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  return libcrux_sha3_Algorithm_Sha224;
}

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_portable_H_DEFINED
#endif /* libcrux_sha3_portable_H */
