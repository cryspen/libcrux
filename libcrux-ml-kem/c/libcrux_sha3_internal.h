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

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_portable_keccak_zero_5a(void) {
  return 0ULL;
}

static KRML_MUSTINLINE uint64_t libcrux_sha3_portable_keccak__veor5q_u64(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  uint64_t ab = a ^ b;
  uint64_t cd = c ^ d;
  uint64_t abcd = ab ^ cd;
  return abcd ^ e;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_portable_keccak_xor5_5a(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  return libcrux_sha3_portable_keccak__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_34(uint64_t x) {
  return x << (uint32_t)(int32_t)1 | x >> (uint32_t)(int32_t)63;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vrax1q_u64(uint64_t a, uint64_t b) {
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_portable_keccak_rotate_left_34(b);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vrax1q_u64(a, b);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vbcaxq_u64(uint64_t a, uint64_t b, uint64_t c) {
  return a ^ (b & ~c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t libcrux_sha3_portable_keccak_and_not_xor_5a(
    uint64_t a, uint64_t b, uint64_t c) {
  return libcrux_sha3_portable_keccak__vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__veorq_n_u64(uint64_t a, uint64_t c) {
  return a ^ c;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_constant_5a(uint64_t a, uint64_t c) {
  return libcrux_sha3_portable_keccak__veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_5a(uint64_t a, uint64_t b) {
  return a ^ b;
}

static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_slice_1(
    Eurydice_slice a[1U], size_t start, size_t len, Eurydice_slice ret[1U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t,
                                     Eurydice_slice);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_slice_n_5a(
    Eurydice_slice a[1U], size_t start, size_t len, Eurydice_slice ret[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, a, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[1U];
  libcrux_sha3_portable_keccak_slice_1(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)1U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE Eurydice_slice_uint8_t_1size_t__x2
libcrux_sha3_portable_keccak_split_at_mut_1(Eurydice_slice out[1U],
                                            size_t mid) {
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at_mut(
      out[0U], mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  Eurydice_slice_uint8_t_1size_t__x2 lit;
  lit.fst[0U] = out00;
  lit.snd[0U] = out01;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE Eurydice_slice_uint8_t_1size_t__x2
libcrux_sha3_portable_keccak_split_at_mut_n_5a(Eurydice_slice a[1U],
                                               size_t mid) {
  return libcrux_sha3_portable_keccak_split_at_mut_1(a, mid);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types uint64_t
with const generics
- $1size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_48_s {
  uint64_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_48;

/**
 Create a new Shake128 x4 state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_1e
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_generic_keccak_new_1e_7a(void) {
  libcrux_sha3_generic_keccak_KeccakState_48 lit;
  lit.st[0U][0U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[0U][1U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[0U][2U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[0U][3U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[0U][4U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[1U][0U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[1U][1U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[1U][2U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[1U][3U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[1U][4U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[2U][0U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[2U][1U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[2U][2U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[2U][3U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[2U][4U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[3U][0U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[3U][1U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[3U][2U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[3U][3U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[3U][4U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[4U][0U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[4U][1U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[4U][2U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[4U][3U] = libcrux_sha3_portable_keccak_zero_5a();
  lit.st[4U][4U] = libcrux_sha3_portable_keccak_zero_5a();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_ac(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_de(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_340(uint64_t x) {
  return x << (uint32_t)(int32_t)36 | x >> (uint32_t)(int32_t)28;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_340(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_65(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_341(uint64_t x) {
  return x << (uint32_t)(int32_t)3 | x >> (uint32_t)(int32_t)61;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e0(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_341(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_650(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_342(uint64_t x) {
  return x << (uint32_t)(int32_t)41 | x >> (uint32_t)(int32_t)23;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e1(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_342(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_651(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_343(uint64_t x) {
  return x << (uint32_t)(int32_t)18 | x >> (uint32_t)(int32_t)46;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e2(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_343(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_652(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e3(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_34(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_653(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e3(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_344(uint64_t x) {
  return x << (uint32_t)(int32_t)44 | x >> (uint32_t)(int32_t)20;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e4(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_344(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_654(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e4(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_345(uint64_t x) {
  return x << (uint32_t)(int32_t)10 | x >> (uint32_t)(int32_t)54;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e5(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_345(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_655(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e5(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_346(uint64_t x) {
  return x << (uint32_t)(int32_t)45 | x >> (uint32_t)(int32_t)19;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e6(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_346(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_656(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e6(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_347(uint64_t x) {
  return x << (uint32_t)(int32_t)2 | x >> (uint32_t)(int32_t)62;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e7(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_347(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_657(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e7(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_348(uint64_t x) {
  return x << (uint32_t)(int32_t)62 | x >> (uint32_t)(int32_t)2;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e8(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_348(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_658(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e8(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_349(uint64_t x) {
  return x << (uint32_t)(int32_t)6 | x >> (uint32_t)(int32_t)58;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e9(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_349(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_659(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3410(uint64_t x) {
  return x << (uint32_t)(int32_t)43 | x >> (uint32_t)(int32_t)21;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e10(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3410(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6510(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3411(uint64_t x) {
  return x << (uint32_t)(int32_t)15 | x >> (uint32_t)(int32_t)49;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e11(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3411(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6511(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3412(uint64_t x) {
  return x << (uint32_t)(int32_t)61 | x >> (uint32_t)(int32_t)3;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e12(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3412(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6512(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3413(uint64_t x) {
  return x << (uint32_t)(int32_t)28 | x >> (uint32_t)(int32_t)36;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e13(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3413(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6513(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3414(uint64_t x) {
  return x << (uint32_t)(int32_t)55 | x >> (uint32_t)(int32_t)9;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e14(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3414(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6514(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3415(uint64_t x) {
  return x << (uint32_t)(int32_t)25 | x >> (uint32_t)(int32_t)39;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e15(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3415(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6515(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3416(uint64_t x) {
  return x << (uint32_t)(int32_t)21 | x >> (uint32_t)(int32_t)43;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e16(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3416(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6516(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3417(uint64_t x) {
  return x << (uint32_t)(int32_t)56 | x >> (uint32_t)(int32_t)8;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e17(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3417(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6517(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3418(uint64_t x) {
  return x << (uint32_t)(int32_t)27 | x >> (uint32_t)(int32_t)37;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e18(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3418(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6518(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3419(uint64_t x) {
  return x << (uint32_t)(int32_t)20 | x >> (uint32_t)(int32_t)44;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e19(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3419(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6519(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3420(uint64_t x) {
  return x << (uint32_t)(int32_t)39 | x >> (uint32_t)(int32_t)25;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e20(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3420(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6520(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e20(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3421(uint64_t x) {
  return x << (uint32_t)(int32_t)8 | x >> (uint32_t)(int32_t)56;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e21(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3421(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6521(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e21(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_3422(uint64_t x) {
  return x << (uint32_t)(int32_t)14 | x >> (uint32_t)(int32_t)50;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6e22(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_3422(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.xor_and_rotate_5a
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6522(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6e22(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_8d(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
  uint64_t c[5U] = {
      libcrux_sha3_portable_keccak_xor5_5a(s->st[0U][0U], s->st[1U][0U],
                                           s->st[2U][0U], s->st[3U][0U],
                                           s->st[4U][0U]),
      libcrux_sha3_portable_keccak_xor5_5a(s->st[0U][1U], s->st[1U][1U],
                                           s->st[2U][1U], s->st[3U][1U],
                                           s->st[4U][1U]),
      libcrux_sha3_portable_keccak_xor5_5a(s->st[0U][2U], s->st[1U][2U],
                                           s->st[2U][2U], s->st[3U][2U],
                                           s->st[4U][2U]),
      libcrux_sha3_portable_keccak_xor5_5a(s->st[0U][3U], s->st[1U][3U],
                                           s->st[2U][3U], s->st[3U][3U],
                                           s->st[4U][3U]),
      libcrux_sha3_portable_keccak_xor5_5a(s->st[0U][4U], s->st[1U][4U],
                                           s->st[2U][4U], s->st[3U][4U],
                                           s->st[4U][4U])};
  uint64_t uu____0 = libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(
      c[((size_t)0U + (size_t)4U) % (size_t)5U],
      c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____1 = libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(
      c[((size_t)1U + (size_t)4U) % (size_t)5U],
      c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____2 = libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(
      c[((size_t)2U + (size_t)4U) % (size_t)5U],
      c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  uint64_t uu____3 = libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(
      c[((size_t)3U + (size_t)4U) % (size_t)5U],
      c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  uint64_t t[5U] = {uu____0, uu____1, uu____2, uu____3,
                    libcrux_sha3_portable_keccak_rotate_left1_and_xor_5a(
                        c[((size_t)4U + (size_t)4U) % (size_t)5U],
                        c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = libcrux_sha3_portable_keccak_xor_5a(s->st[0U][0U], t[0U]);
  s->st[1U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_65(s->st[1U][0U], t[0U]);
  s->st[2U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_650(s->st[2U][0U], t[0U]);
  s->st[3U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_651(s->st[3U][0U], t[0U]);
  s->st[4U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_652(s->st[4U][0U], t[0U]);
  s->st[0U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_653(s->st[0U][1U], t[1U]);
  s->st[1U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_654(s->st[1U][1U], t[1U]);
  s->st[2U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_655(s->st[2U][1U], t[1U]);
  s->st[3U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_656(s->st[3U][1U], t[1U]);
  s->st[4U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_657(s->st[4U][1U], t[1U]);
  s->st[0U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_658(s->st[0U][2U], t[2U]);
  s->st[1U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_659(s->st[1U][2U], t[2U]);
  s->st[2U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6510(s->st[2U][2U], t[2U]);
  s->st[3U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6511(s->st[3U][2U], t[2U]);
  s->st[4U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6512(s->st[4U][2U], t[2U]);
  s->st[0U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6513(s->st[0U][3U], t[3U]);
  s->st[1U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6514(s->st[1U][3U], t[3U]);
  s->st[2U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6515(s->st[2U][3U], t[3U]);
  s->st[3U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6516(s->st[3U][3U], t[3U]);
  s->st[4U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6517(s->st[4U][3U], t[3U]);
  s->st[0U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6518(s->st[0U][4U], t[4U]);
  s->st[1U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6519(s->st[1U][4U], t[4U]);
  s->st[2U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6520(s->st[2U][4U], t[4U]);
  s->st[3U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6521(s->st[3U][4U], t[4U]);
  uint64_t uu____27 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6522(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_ac(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
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
A monomorphic instance of libcrux_sha3.generic_keccak.chi
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_c7(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
  uint64_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(uint64_t[5U]));
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR5(
          i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i;
          s->st[i1][j] = libcrux_sha3_portable_keccak_and_not_xor_5a(
              s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
              old[i1][(j + (size_t)1U) % (size_t)5U]);););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_4f(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, size_t i) {
  s->st[0U][0U] = libcrux_sha3_portable_keccak_xor_constant_5a(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_13(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_8d(s);
    libcrux_sha3_generic_keccak_pi_ac(s);
    libcrux_sha3_generic_keccak_chi_c7(s);
    libcrux_sha3_generic_keccak_iota_4f(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_25(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_39(
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_48(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_39(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c8(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_48(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_58(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_48(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de0(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_ac0(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_de0(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d0(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_250(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d0(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_390(
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_480(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_390(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_580(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_480(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c80(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_480(s->st, out);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df3(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_de(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_243(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_df3(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_e03(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_39(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak_store_block_full_5a_883(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_e03(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_653(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_883(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_123(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_883(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)168U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)168U,
                                            (size_t)168U, ret);
    libcrux_sha3_generic_keccak_absorb_block_243(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)168U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_25(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_653(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_58(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)168U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c8(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_123(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf4(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de3(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df2(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_de3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_242(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_df2(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_ac3(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_de3(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d3(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_254(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d3(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_393(
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
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_e02(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_393(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak_store_block_full_5a_882(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_e02(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_652(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_882(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_483(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_393(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_583(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_483(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c83(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_483(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_122(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_882(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf3(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)104U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)104U,
                                            (size_t)104U, ret);
    libcrux_sha3_generic_keccak_absorb_block_242(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_254(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_652(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)104U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_583(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)104U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c83(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_122(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd3(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf3(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de2(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df1(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_de2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_241(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_df1(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_ac2(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_de2(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d2(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_253(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d2(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_392(
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
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_e01(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_392(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak_store_block_full_5a_881(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_e01(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_651(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_881(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_482(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_392(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_582(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_482(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c82(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_482(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_121(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_881(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf2(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)144U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)144U,
                                            (size_t)144U, ret);
    libcrux_sha3_generic_keccak_absorb_block_241(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_253(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_651(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)144U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_582(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)144U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c82(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_121(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd2(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf2(uu____0, out);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df0(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_de0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_240(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_df0(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_e00(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_390(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak_store_block_full_5a_880(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_e00(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_650(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_880(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_120(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_880(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf1(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)136U,
                                            (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_240(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_250(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_650(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_580(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c80(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_120(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd1(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf1(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_252(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d0(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)136U,
                                            (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_240(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_252(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_650(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_580(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c80(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_120(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf0(uu____0, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de1(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t,
                                 Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    s[uu____1][uu____2] =
        s[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_de1(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_24(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_df(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_ac1(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_de1(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d1(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac1(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_251(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d1(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_391(
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
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_e0(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_391(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_88(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_e0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_65(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_88(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_481(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_391(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_581(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_481(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c81(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_481(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_12(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_88(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_b3 lit;
    lit.start = (size_t)0U;
    lit.end = core_slice___Slice_T___len(out[i], uint8_t, size_t);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_b3, Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_cf(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_7a();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)72U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_48 *uu____0 = &s;
    Eurydice_slice uu____1[1U];
    memcpy(uu____1, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(uu____1, i0 * (size_t)72U,
                                            (size_t)72U, ret);
    libcrux_sha3_generic_keccak_absorb_block_24(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState_48 *uu____2 = &s;
  Eurydice_slice uu____3[1U];
  memcpy(uu____3, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_251(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_65(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)72U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_581(&s, o0);
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
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)72U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c81(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_12(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf(uu____0, out);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_internal_H_DEFINED
#endif
