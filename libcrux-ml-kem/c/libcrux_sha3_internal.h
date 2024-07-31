/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 013beb9e4046a151131c6a56dfe25e606b49c4a1
 * Karamel: 4626e5fcb3787a47c806d160539342ade4b0809c
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: 8a3c1c4c84f258580d53bfef5ad2b1b7d5ef5fca
 */

#ifndef __libcrux_sha3_internal_H
#define __libcrux_sha3_internal_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

static const uint64_t libcrux_sha3_generic_keccak_ROUNDCONSTANTS[24U] = {
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

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero(
    void) {
  return 0ULL;
}

static KRML_MUSTINLINE uint64_t libcrux_sha3_portable_keccak__veor5q_u64(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  uint64_t ab = a ^ b;
  uint64_t cd = c ^ d;
  uint64_t abcd = ab ^ cd;
  return abcd ^ e;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  return libcrux_sha3_portable_keccak__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_70(uint64_t x) {
  return x << (uint32_t)(int32_t)1 | x >> (uint32_t)(int32_t)63;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vrax1q_u64(uint64_t a, uint64_t b) {
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_portable_keccak_rotate_left_70(b);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vrax1q_u64(a, b);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vbcaxq_u64(uint64_t a, uint64_t b, uint64_t c) {
  return a ^ (b & ~c);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___and_not_xor(
    uint64_t a, uint64_t b, uint64_t c) {
  return libcrux_sha3_portable_keccak__vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__veorq_n_u64(uint64_t a, uint64_t c) {
  return a ^ c;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_constant(
    uint64_t a, uint64_t c) {
  return libcrux_sha3_portable_keccak__veorq_n_u64(a, c);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor(
    uint64_t a, uint64_t b) {
  return a ^ b;
}

static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_slice_1(
    Eurydice_slice a[1U], size_t start, size_t len, Eurydice_slice ret[1U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t,
                                     Eurydice_slice);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
    Eurydice_slice a[1U], size_t start, size_t len, Eurydice_slice ret[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, a, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[1U];
  libcrux_sha3_portable_keccak_slice_1(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)1U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_
    libcrux_sha3_portable_keccak_split_at_mut_1(Eurydice_slice out[1U],
                                                size_t mid) {
  K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t uu____0 =
      core_slice___Slice_T___split_at_mut(
          out[0U], mid, uint8_t,
          K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ lit;
  lit.fst[0U] = out00;
  lit.snd[0U] = out01;
  return lit;
}

static KRML_MUSTINLINE
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
        Eurydice_slice a[1U], size_t mid) {
  return libcrux_sha3_portable_keccak_split_at_mut_1(a, mid);
}

typedef struct libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t_s {
  uint64_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t;

/**
A monomorphic instance of
libcrux_sha3.generic_keccak.{libcrux_sha3::generic_keccak::KeccakState<T,␣N>[TraitClause@0]#1}.new
with types uint64_t and with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93(
    void) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t lit;
  lit.st[0U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[0U][1U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[0U][2U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[0U][3U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[0U][4U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[1U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[1U][1U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[1U][2U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[1U][3U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[1U][4U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[2U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[2U][1U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[2U][2U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[2U][3U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[2U][4U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[3U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[3U][1U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[3U][2U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[3U][3U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[3U][4U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[4U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[4U][1U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[4U][2U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[4U][3U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  lit.st[4U][4U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___zero();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block with const
generics:
- RATE = 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_66(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result__core__result__Result_T__E___unwrap_15(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full with
const generics:
- RATE = 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_66(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_66(s, buf);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block_full
with const generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_66(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_66(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_71(uint64_t x) {
  return x << (uint32_t)(int32_t)36 | x >> (uint32_t)(int32_t)28;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_71(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_71(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 36
- RIGHT = 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_71(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_71(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_08(uint64_t x) {
  return x << (uint32_t)(int32_t)3 | x >> (uint32_t)(int32_t)61;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_08(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_08(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 3
- RIGHT = 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_08(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_08(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_6a(uint64_t x) {
  return x << (uint32_t)(int32_t)41 | x >> (uint32_t)(int32_t)23;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6a(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_6a(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 41
- RIGHT = 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_6a(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_95(uint64_t x) {
  return x << (uint32_t)(int32_t)18 | x >> (uint32_t)(int32_t)46;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_95(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_95(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 18
- RIGHT = 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_95(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_95(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_70(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_70(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 1
- RIGHT = 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_70(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_70(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_e1(uint64_t x) {
  return x << (uint32_t)(int32_t)44 | x >> (uint32_t)(int32_t)20;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_e1(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_e1(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 44
- RIGHT = 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_e1(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_e1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_ce(uint64_t x) {
  return x << (uint32_t)(int32_t)10 | x >> (uint32_t)(int32_t)54;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_ce(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_ce(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 10
- RIGHT = 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_ce(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_b6(uint64_t x) {
  return x << (uint32_t)(int32_t)45 | x >> (uint32_t)(int32_t)19;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_b6(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_b6(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 45
- RIGHT = 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_b6(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_b6(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_2a(uint64_t x) {
  return x << (uint32_t)(int32_t)2 | x >> (uint32_t)(int32_t)62;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_2a(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_2a(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 2
- RIGHT = 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_2a(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_2a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_25(uint64_t x) {
  return x << (uint32_t)(int32_t)62 | x >> (uint32_t)(int32_t)2;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_25(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_25(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 62
- RIGHT = 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_25(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_4b(uint64_t x) {
  return x << (uint32_t)(int32_t)6 | x >> (uint32_t)(int32_t)58;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_4b(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_4b(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 6
- RIGHT = 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_4b(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_4b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_c2(uint64_t x) {
  return x << (uint32_t)(int32_t)43 | x >> (uint32_t)(int32_t)21;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_c2(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_c2(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 43
- RIGHT = 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_c2(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_c2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3e(uint64_t x) {
  return x << (uint32_t)(int32_t)15 | x >> (uint32_t)(int32_t)49;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3e(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3e(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 15
- RIGHT = 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_3e(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3e(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_bd(uint64_t x) {
  return x << (uint32_t)(int32_t)61 | x >> (uint32_t)(int32_t)3;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_bd(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_bd(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 61
- RIGHT = 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_bd(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_bd(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_42(uint64_t x) {
  return x << (uint32_t)(int32_t)28 | x >> (uint32_t)(int32_t)36;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_42(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_42(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 28
- RIGHT = 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_42(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_42(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_64(uint64_t x) {
  return x << (uint32_t)(int32_t)55 | x >> (uint32_t)(int32_t)9;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_64(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_64(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 55
- RIGHT = 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_64(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_64(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_cc(uint64_t x) {
  return x << (uint32_t)(int32_t)25 | x >> (uint32_t)(int32_t)39;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_cc(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_cc(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 25
- RIGHT = 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_cc(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_cc(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_d5(uint64_t x) {
  return x << (uint32_t)(int32_t)21 | x >> (uint32_t)(int32_t)43;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_d5(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_d5(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 21
- RIGHT = 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_d5(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_d5(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_61(uint64_t x) {
  return x << (uint32_t)(int32_t)56 | x >> (uint32_t)(int32_t)8;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_61(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_61(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 56
- RIGHT = 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_61(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_61(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_6f(uint64_t x) {
  return x << (uint32_t)(int32_t)27 | x >> (uint32_t)(int32_t)37;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6f(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_6f(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 27
- RIGHT = 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_6f(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_06(uint64_t x) {
  return x << (uint32_t)(int32_t)20 | x >> (uint32_t)(int32_t)44;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_06(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_06(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 20
- RIGHT = 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_06(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_06(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3d(uint64_t x) {
  return x << (uint32_t)(int32_t)39 | x >> (uint32_t)(int32_t)25;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3d(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 39
- RIGHT = 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_3d(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_0c(uint64_t x) {
  return x << (uint32_t)(int32_t)8 | x >> (uint32_t)(int32_t)56;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_0c(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_0c(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 8
- RIGHT = 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_0c(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_0c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left with const
generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_98(uint64_t x) {
  return x << (uint32_t)(int32_t)14 | x >> (uint32_t)(int32_t)50;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64 with const
generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_98(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_98(ab);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.xor_and_rotate
with const generics:
- LEFT = 14
- RIGHT = 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_98(
    uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_98(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho with types
uint64_t and with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_93(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s) {
  uint64_t c[5U] = {
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
          s->st[0U][0U], s->st[1U][0U], s->st[2U][0U], s->st[3U][0U],
          s->st[4U][0U]),
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
          s->st[0U][1U], s->st[1U][1U], s->st[2U][1U], s->st[3U][1U],
          s->st[4U][1U]),
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
          s->st[0U][2U], s->st[1U][2U], s->st[2U][2U], s->st[3U][2U],
          s->st[4U][2U]),
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
          s->st[0U][3U], s->st[1U][3U], s->st[2U][3U], s->st[3U][3U],
          s->st[4U][3U]),
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor5(
          s->st[0U][4U], s->st[1U][4U], s->st[2U][4U], s->st[3U][4U],
          s->st[4U][4U])};
  uint64_t uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
          c[((size_t)0U + (size_t)4U) % (size_t)5U],
          c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____1 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
          c[((size_t)1U + (size_t)4U) % (size_t)5U],
          c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____2 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
          c[((size_t)2U + (size_t)4U) % (size_t)5U],
          c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____3 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
          c[((size_t)3U + (size_t)4U) % (size_t)5U],
          c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  uint64_t t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___rotate_left1_and_xor(
          c[((size_t)4U + (size_t)4U) % (size_t)5U],
          c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor(
          s->st[0U][0U], t[0U]);
  uint64_t uu____4 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_71(
          s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  uint64_t uu____5 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_08(
          s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  uint64_t uu____6 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_6a(
          s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  uint64_t uu____7 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_95(
          s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  uint64_t uu____8 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_70(
          s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  uint64_t uu____9 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_e1(
          s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  uint64_t uu____10 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_ce(
          s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  uint64_t uu____11 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_b6(
          s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  uint64_t uu____12 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_2a(
          s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  uint64_t uu____13 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_25(
          s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  uint64_t uu____14 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_4b(
          s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  uint64_t uu____15 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_c2(
          s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  uint64_t uu____16 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_3e(
          s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  uint64_t uu____17 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_bd(
          s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  uint64_t uu____18 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_42(
          s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  uint64_t uu____19 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_64(
          s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  uint64_t uu____20 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_cc(
          s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  uint64_t uu____21 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_d5(
          s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  uint64_t uu____22 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_61(
          s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  uint64_t uu____23 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_6f(
          s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  uint64_t uu____24 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_06(
          s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  uint64_t uu____25 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_3d(
          s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  uint64_t uu____26 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_0c(
          s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
  uint64_t uu____27 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_and_rotate_98(
          s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi with types uint64_t and
with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_93(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s) {
  uint64_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(uint64_t[5U]));
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
A monomorphic instance of libcrux_sha3.generic_keccak.chi with types uint64_t
and with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_93(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s) {
  uint64_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(uint64_t[5U]));
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR5(
          i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i;
          s->st[i1][j] =
              libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___and_not_xor(
                  s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
                  old[i1][(j + (size_t)1U) % (size_t)5U]);););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota with types uint64_t
and with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_93(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s, size_t i) {
  s->st[0U][0U] =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___xor_constant(
          s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600 with types
uint64_t and with const generics:
- N = 1
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_93(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_93(s);
    libcrux_sha3_generic_keccak_pi_93(s);
    libcrux_sha3_generic_keccak_chi_93(s);
    libcrux_sha3_generic_keccak_iota_93(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 168
- DELIM = 31
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_f7(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 31U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)168U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_66(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block with const
generics:
- RATE = 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_66(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t,
        Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block
with const generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_66(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_66(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types uint64_t and with const generics:
- N = 1
- RATE = 168
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_fd(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_66(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types uint64_t and with const generics:
- N = 1
- RATE = 168
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_fd(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_66(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_35(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result__core__result__Result_T__E___unwrap_15(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full with
const generics:
- RATE = 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_35(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_35(s, buf);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block_full
with const generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_35(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_35(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 136
- DELIM = 31
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_78(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 31U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_35(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block with const
generics:
- RATE = 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_35(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t,
        Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block
with const generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_35(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_35(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types uint64_t and with const generics:
- N = 1
- RATE = 136
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_43(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_35(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types uint64_t and with const generics:
- N = 1
- RATE = 136
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_43(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_35(
      s->st, out);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block
with const generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_660(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_66(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
uint64_t and with const generics:
- N = 1
- RATE = 168
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_fd(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_660(
      uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full with
const generics:
- RATE = 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_660(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_66(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block_full
with const generics:
- BLOCKSIZE = 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_660(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_660(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t and with const generics:
- N = 1
- RATE = 168
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_fd(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_660(
      s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
uint64_t and with const generics:
- N = 1
- RATE = 168
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_fd(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_660(
      s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 168
- DELIM = 31
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_f7(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)168U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)168U, (size_t)168U, ret);
    libcrux_sha3_generic_keccak_absorb_block_fd(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)168U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_f7(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_fd(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)168U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_fd(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)168U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_fd(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_fd(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 168
- DELIM = 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_e0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_f7(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_d4(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result__core__result__Result_T__E___unwrap_15(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block
with const generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_d4(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_d4(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
uint64_t and with const generics:
- N = 1
- RATE = 104
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_a0(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_d4(
      uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full with
const generics:
- RATE = 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_d4(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_d4(s, buf);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block_full
with const generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_d4(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_d4(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 104
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_c3(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)104U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_d4(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block with const
generics:
- RATE = 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_d4(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t,
        Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full with
const generics:
- RATE = 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_d4(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_d4(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block_full
with const generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_d4(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_d4(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t and with const generics:
- N = 1
- RATE = 104
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_a0(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_d4(
      s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block
with const generics:
- BLOCKSIZE = 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_d4(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_d4(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types uint64_t and with const generics:
- N = 1
- RATE = 104
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_a0(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_d4(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types uint64_t and with const generics:
- N = 1
- RATE = 104
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_a0(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_d4(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
uint64_t and with const generics:
- N = 1
- RATE = 104
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_a0(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_d4(
      s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 104
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_c3(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)104U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)104U, (size_t)104U, ret);
    libcrux_sha3_generic_keccak_absorb_block_a0(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_c3(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_a0(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)104U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_a0(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)104U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_a0(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_a0(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 104
- DELIM = 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_b6(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_c3(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_f0(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result__core__result__Result_T__E___unwrap_15(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block
with const generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_f0(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_f0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
uint64_t and with const generics:
- N = 1
- RATE = 144
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_57(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_f0(
      uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full with
const generics:
- RATE = 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_f0(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_f0(s, buf);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block_full
with const generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_f0(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_f0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 144
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_f4(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)144U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_f0(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block with const
generics:
- RATE = 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_f0(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t,
        Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full with
const generics:
- RATE = 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_f0(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_f0(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block_full
with const generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_f0(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_f0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t and with const generics:
- N = 1
- RATE = 144
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_57(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_f0(
      s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block
with const generics:
- BLOCKSIZE = 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_f0(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_f0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types uint64_t and with const generics:
- N = 1
- RATE = 144
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_57(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_f0(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types uint64_t and with const generics:
- N = 1
- RATE = 144
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_57(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_f0(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
uint64_t and with const generics:
- N = 1
- RATE = 144
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_57(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_f0(
      s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 144
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_f4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)144U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)144U, (size_t)144U, ret);
    libcrux_sha3_generic_keccak_absorb_block_57(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_f4(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_57(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)144U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_57(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)144U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_57(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_57(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 144
- DELIM = 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_d4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_f4(uu____0, out);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block
with const generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_35(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_35(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
uint64_t and with const generics:
- N = 1
- RATE = 136
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_43(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_35(
      uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full with
const generics:
- RATE = 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_35(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_35(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block_full
with const generics:
- BLOCKSIZE = 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_35(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_35(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t and with const generics:
- N = 1
- RATE = 136
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_43(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_35(
      s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
uint64_t and with const generics:
- N = 1
- RATE = 136
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_43(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_35(
      s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 136
- DELIM = 31
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_780(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_43(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_78(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_43(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_43(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_43(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_43(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 136
- DELIM = 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_d2(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_780(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 136
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_780(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_35(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 136
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_78(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_43(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_780(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_43(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_43(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_43(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_43(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 136
- DELIM = 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2f(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_78(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_660(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result__core__result__Result_T__E___unwrap_15(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block
with const generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_66(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_660(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block with types
uint64_t and with const generics:
- N = 1
- RATE = 72
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_5a(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_66(
      uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full with
const generics:
- RATE = 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_660(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_660(s, buf);
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.load_block_full
with const generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_660(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_660(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final with types
uint64_t and with const generics:
- N = 1
- RATE = 72
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_21(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i], uint8_t, void *);
    }
    blocks[i][last_len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)72U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full_660(
      uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block with const
generics:
- RATE = 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_660(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t,
        Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full with
const generics:
- RATE = 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_66(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_660(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block_full
with const generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_66(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_66(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t and with const generics:
- N = 1
- RATE = 72
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5a(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_66(
      s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of
libcrux_sha3.portable_keccak.{(libcrux_sha3::traits::internal::KeccakItem<1:␣usize>␣for␣u64)}.store_block
with const generics:
- BLOCKSIZE = 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_660(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_660(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block with
types uint64_t and with const generics:
- N = 1
- RATE = 72
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_5a(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_660(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block with
types uint64_t and with const generics:
- N = 1
- RATE = 72
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5a(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(s);
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_660(
      s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last with types
uint64_t and with const generics:
- N = 1
- RATE = 72
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_5a(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s,
    Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_93(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store_block_full_66(
      s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range__size_t lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range__size_t,
                                   Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak with types uint64_t
and with const generics:
- N = 1
- RATE = 72
- DELIM = 6
Furthermore, this instances features the following traits:
- {(libcrux_sha3::traits::internal::KeccakItem<1: usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_21(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t s =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new_93();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)72U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____1, i0 * (size_t)72U, (size_t)72U, ret);
    libcrux_sha3_generic_keccak_absorb_block_5a(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_21(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5a(&s, out);
  } else {
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____4 =
        libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
            out, (size_t)72U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_5a(&s, o0);
    core_ops_range_Range__size_t iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)1U,
                                                    .end = blocks}),
            core_ops_range_Range__size_t, core_ops_range_Range__size_t);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A___6__next(
              &iter, size_t, core_option_Option__size_t)
              .tag == core_option_None) {
        break;
      } else {
        K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____5 =
            libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
                o1, (size_t)72U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5a(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_5a(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1 with const generics:
- RATE = 72
- DELIM = 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_26(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_21(uu____0, out);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_internal_H_DEFINED
#endif
