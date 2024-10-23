/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45f5a34f336e35c6cc2253bc90cbdb8d812cefa9
 * Eurydice: 1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c
 * Karamel: 8c3612018c25889288da6857771be3ad03b75bcd
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 897008ee57eed9e4574222a5e96d306ce203ecee
 */

#ifndef __libcrux_sha3_portable_H
#define __libcrux_sha3_portable_H

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
libcrux_sha3_portable_keccak_rotate_left_76(uint64_t x) {
  return x << (uint32_t)(int32_t)1 | x >> (uint32_t)(int32_t)63;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vrax1q_u64(uint64_t a, uint64_t b) {
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_portable_keccak_rotate_left_76(b);
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
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_slice_n_5a(
    Eurydice_slice a[1U], size_t start, size_t len, Eurydice_slice ret[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_a[1U];
  memcpy(copy_of_a, a, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[1U];
  libcrux_sha3_portable_keccak_slice_1(copy_of_a, start, len, ret0);
  memcpy(ret, ret0, (size_t)1U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE Eurydice_slice_uint8_t_1size_t__x2
libcrux_sha3_portable_keccak_split_at_mut_1(Eurydice_slice out[1U],
                                            size_t mid) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at_mut(
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
typedef struct libcrux_sha3_generic_keccak_KeccakState_17_s {
  uint64_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_17;

/**
 Create a new Shake128 x4 state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_89
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_generic_keccak_new_89_04(void) {
  libcrux_sha3_generic_keccak_KeccakState_17 lit;
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
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_f8(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U]);
    unwrap_26_68(dst, uu____0);
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
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_f8(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[1U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_f8(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_02(uint64_t x) {
  return x << (uint32_t)(int32_t)36 | x >> (uint32_t)(int32_t)28;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_02(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_02(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_02(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_ac(uint64_t x) {
  return x << (uint32_t)(int32_t)3 | x >> (uint32_t)(int32_t)61;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_ac(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_ac(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_ac(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_020(uint64_t x) {
  return x << (uint32_t)(int32_t)41 | x >> (uint32_t)(int32_t)23;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_020(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_020(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_020(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_a9(uint64_t x) {
  return x << (uint32_t)(int32_t)18 | x >> (uint32_t)(int32_t)46;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_a9(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_a9(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_a9(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_76(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_76(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_76(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_58(uint64_t x) {
  return x << (uint32_t)(int32_t)44 | x >> (uint32_t)(int32_t)20;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_58(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_58(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_58(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_e0(uint64_t x) {
  return x << (uint32_t)(int32_t)10 | x >> (uint32_t)(int32_t)54;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_e0(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_e0(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_e0(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_63(uint64_t x) {
  return x << (uint32_t)(int32_t)45 | x >> (uint32_t)(int32_t)19;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_63(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_63(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_63(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_6a(uint64_t x) {
  return x << (uint32_t)(int32_t)2 | x >> (uint32_t)(int32_t)62;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6a(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_6a(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6a(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_ab(uint64_t x) {
  return x << (uint32_t)(int32_t)62 | x >> (uint32_t)(int32_t)2;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_ab(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_ab(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_ab(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_5b(uint64_t x) {
  return x << (uint32_t)(int32_t)6 | x >> (uint32_t)(int32_t)58;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_5b(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_5b(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_5b(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_6f(uint64_t x) {
  return x << (uint32_t)(int32_t)43 | x >> (uint32_t)(int32_t)21;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_6f(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_6f(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_6f(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_62(uint64_t x) {
  return x << (uint32_t)(int32_t)15 | x >> (uint32_t)(int32_t)49;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_62(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_62(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_62(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_23(uint64_t x) {
  return x << (uint32_t)(int32_t)61 | x >> (uint32_t)(int32_t)3;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_23(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_23(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_23(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_37(uint64_t x) {
  return x << (uint32_t)(int32_t)28 | x >> (uint32_t)(int32_t)36;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_37(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_37(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_37(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_bb(uint64_t x) {
  return x << (uint32_t)(int32_t)55 | x >> (uint32_t)(int32_t)9;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_bb(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_bb(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_bb(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_b9(uint64_t x) {
  return x << (uint32_t)(int32_t)25 | x >> (uint32_t)(int32_t)39;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_b9(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_b9(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_b9(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_54(uint64_t x) {
  return x << (uint32_t)(int32_t)21 | x >> (uint32_t)(int32_t)43;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_54(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_54(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_54(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_4c(uint64_t x) {
  return x << (uint32_t)(int32_t)56 | x >> (uint32_t)(int32_t)8;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_4c(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_4c(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_4c(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_ce(uint64_t x) {
  return x << (uint32_t)(int32_t)27 | x >> (uint32_t)(int32_t)37;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_ce(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_ce(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_ce(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_77(uint64_t x) {
  return x << (uint32_t)(int32_t)20 | x >> (uint32_t)(int32_t)44;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_77(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_77(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_77(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_25(uint64_t x) {
  return x << (uint32_t)(int32_t)39 | x >> (uint32_t)(int32_t)25;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_25(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_25(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_25(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_af(uint64_t x) {
  return x << (uint32_t)(int32_t)8 | x >> (uint32_t)(int32_t)56;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_af(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_af(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_af(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_fd(uint64_t x) {
  return x << (uint32_t)(int32_t)14 | x >> (uint32_t)(int32_t)50;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_fd(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_fd(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_fd(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_fd(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *s) {
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
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_02(s->st[1U][0U], t[0U]);
  s->st[2U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_ac(s->st[2U][0U], t[0U]);
  s->st[3U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_020(s->st[3U][0U], t[0U]);
  s->st[4U][0U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_a9(s->st[4U][0U], t[0U]);
  s->st[0U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_76(s->st[0U][1U], t[1U]);
  s->st[1U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_58(s->st[1U][1U], t[1U]);
  s->st[2U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_e0(s->st[2U][1U], t[1U]);
  s->st[3U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_63(s->st[3U][1U], t[1U]);
  s->st[4U][1U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6a(s->st[4U][1U], t[1U]);
  s->st[0U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_ab(s->st[0U][2U], t[2U]);
  s->st[1U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_5b(s->st[1U][2U], t[2U]);
  s->st[2U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6f(s->st[2U][2U], t[2U]);
  s->st[3U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_62(s->st[3U][2U], t[2U]);
  s->st[4U][2U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_23(s->st[4U][2U], t[2U]);
  s->st[0U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_37(s->st[0U][3U], t[3U]);
  s->st[1U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_bb(s->st[1U][3U], t[3U]);
  s->st[2U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_b9(s->st[2U][3U], t[3U]);
  s->st[3U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_54(s->st[3U][3U], t[3U]);
  s->st[4U][3U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_4c(s->st[4U][3U], t[3U]);
  s->st[0U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_ce(s->st[0U][4U], t[4U]);
  s->st[1U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_77(s->st[1U][4U], t[4U]);
  s->st[2U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_25(s->st[2U][4U], t[4U]);
  s->st[3U][4U] =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_af(s->st[3U][4U], t[4U]);
  uint64_t uu____27 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_fd(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *s) {
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *s) {
  uint64_t old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(uint64_t[5U]));
  for (size_t i0 = (size_t)0U; i0 < (size_t)5U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t j = i;
      s->st[i1][j] = libcrux_sha3_portable_keccak_and_not_xor_5a(
          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
          old[i1][(j + (size_t)1U) % (size_t)5U]);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, size_t i) {
  s->st[0U][0U] = libcrux_sha3_portable_keccak_xor_constant_5a(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_04(s);
    libcrux_sha3_generic_keccak_pi_04(s);
    libcrux_sha3_generic_keccak_chi_04(s);
    libcrux_sha3_generic_keccak_iota_04(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_f8(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_f8(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t)};
  libcrux_sha3_portable_keccak_load_block_f8(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_f8(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[1U][200U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_f8(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)72U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_f8(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_f8(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_f8(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t)};
  libcrux_sha3_portable_keccak_store_block_f8(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out[200U];
  memcpy(copy_of_out, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_f8(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_f8(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_f8(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_f8(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_f8(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_f8(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_f8(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_f8(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)72U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)72U,
                                            (size_t)72U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c6(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c6(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)72U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c6(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)72U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c6(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c6(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_96(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e(copy_of_data, out);
}

/**
 A portable SHA3 512 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha512(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_96(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5b(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U]);
    unwrap_26_68(dst, uu____0);
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
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_5b(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[1U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5b(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_5b(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5b(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t)};
  libcrux_sha3_portable_keccak_load_block_5b(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_5b(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[1U][200U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5b(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e0(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5b(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5b(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t)};
  libcrux_sha3_portable_keccak_store_block_5b(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out[200U];
  memcpy(copy_of_out, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_5b(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_5b(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_5b(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_5b(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_5b(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)136U,
                                            (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c60(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e0(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c60(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c60(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c60(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c60(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_ad(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e0(copy_of_data, out);
}

/**
 A portable SHA3 256 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha256(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_ad(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e1(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e1(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)136U,
                                            (size_t)136U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c60(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e1(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c60(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c60(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c60(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c60(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_ad0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e1(copy_of_data, out);
}

/**
 A portable SHAKE256 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_shake256(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_ad0(buf0, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_17
    libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_89_04();
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_3a(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U]);
    unwrap_26_68(dst, uu____0);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_3a(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t)};
  libcrux_sha3_portable_keccak_load_block_3a(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_3a(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[1U][200U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_3a(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e2(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_3a(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
 Absorb
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_9e2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_3a(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_3a(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_3a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_3a(s->st, out);
}

/**
 Squeeze another block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_3a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_c61(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o2);
}

/**
 Squeeze three blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_c6(s, buf);
}

#define libcrux_sha3_Sha224 0
#define libcrux_sha3_Sha256 1
#define libcrux_sha3_Sha384 2
#define libcrux_sha3_Sha512 3

typedef uint8_t libcrux_sha3_Algorithm;

/**
 Returns the output size of a digest.
*/
static inline size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode) {
  size_t uu____0;
  switch (mode) {
    case libcrux_sha3_Sha224: {
      uu____0 = (size_t)28U;
      break;
    }
    case libcrux_sha3_Sha256: {
      uu____0 = (size_t)32U;
      break;
    }
    case libcrux_sha3_Sha384: {
      uu____0 = (size_t)48U;
      break;
    }
    case libcrux_sha3_Sha512: {
      uu____0 = (size_t)64U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return uu____0;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_2c(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U]);
    unwrap_26_68(dst, uu____0);
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
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_2c(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[1U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_2c(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_2c(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_2c(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t)};
  libcrux_sha3_portable_keccak_load_block_2c(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2c(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[1U][200U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_2c(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e3(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)144U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_2c(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_2c(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_2c(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t)};
  libcrux_sha3_portable_keccak_store_block_2c(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out[200U];
  memcpy(copy_of_out, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_2c(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_2c(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_2c(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_2c(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_2c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_2c(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_2c(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_2c(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e2(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)144U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)144U,
                                            (size_t)144U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c61(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e3(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c61(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)144U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c62(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)144U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c62(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c61(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_1e(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e2(copy_of_data, out);
}

/**
 A portable SHA3 224 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_1e(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_7a(
    uint64_t (*s)[5U], Eurydice_slice blocks[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    uint8_t uu____0[8U];
    Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[0U], (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U]);
    unwrap_26_68(dst, uu____0);
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
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_7a(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[1U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_7a(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_7a(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t)};
  libcrux_sha3_portable_keccak_load_block_7a(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full_5a
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_7a(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[1U][200U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e4(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice last[1U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t);
      Eurydice_slice_copy(uu____0, last[i0], uint8_t);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)104U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_7a(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_7a(
    uint64_t (*s)[5U], Eurydice_slice out[1U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(s[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_7a(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t)};
  libcrux_sha3_portable_keccak_store_block_7a(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out[200U];
  memcpy(copy_of_out, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_7a(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_7a(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_7a(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_7a(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_7a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_7a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_7a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_7a(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e3(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)104U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)104U,
                                            (size_t)104U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c62(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e4(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c62(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)104U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c63(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)104U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c63(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c62(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_7c(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e3(copy_of_data, out);
}

/**
 A portable SHA3 384 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_7c(buf0, buf);
}

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
static KRML_MUSTINLINE void libcrux_sha3_sha224_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha224(digest, payload);
}

/**
 SHA3 224
*/
static KRML_MUSTINLINE void libcrux_sha3_sha224(Eurydice_slice data,
                                                uint8_t ret[28U]) {
  uint8_t out[28U] = {0U};
  libcrux_sha3_sha224_ema(Eurydice_array_to_slice((size_t)28U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)28U * sizeof(uint8_t));
}

/**
 SHA3 256
*/
static KRML_MUSTINLINE void libcrux_sha3_sha256_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha256(digest, payload);
}

/**
 SHA3 256
*/
static KRML_MUSTINLINE void libcrux_sha3_sha256(Eurydice_slice data,
                                                uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  libcrux_sha3_sha256_ema(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
 SHA3 384
*/
static KRML_MUSTINLINE void libcrux_sha3_sha384_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha384(digest, payload);
}

/**
 SHA3 384
*/
static KRML_MUSTINLINE void libcrux_sha3_sha384(Eurydice_slice data,
                                                uint8_t ret[48U]) {
  uint8_t out[48U] = {0U};
  libcrux_sha3_sha384_ema(Eurydice_array_to_slice((size_t)48U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)48U * sizeof(uint8_t));
}

/**
 SHA3 512
*/
static KRML_MUSTINLINE void libcrux_sha3_sha512_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha512(digest, payload);
}

/**
 SHA3 512
*/
static KRML_MUSTINLINE void libcrux_sha3_sha512(Eurydice_slice data,
                                                uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  libcrux_sha3_sha512_ema(Eurydice_array_to_slice((size_t)64U, out, uint8_t),
                          data);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_3a(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[1U];
  memcpy(copy_of_b, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_3a(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_3a(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_3a(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t)};
  libcrux_sha3_portable_keccak_store_block_3a(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out[200U];
  memcpy(copy_of_out, out, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_3a(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_3a(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_3a(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_04(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_3a(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = out[i0];
    uint8_t *uu____1 = b[i0];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i0], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08),
        uint8_t);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)168U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[1U];
    memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(copy_of_data, i0 * (size_t)168U,
                                            (size_t)168U, ret);
    libcrux_sha3_generic_keccak_absorb_block_c63(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)168U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice ret[1U];
  libcrux_sha3_portable_keccak_slice_n_5a(
      copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem, ret);
  libcrux_sha3_generic_keccak_absorb_final_9e2(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c63(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c61(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, Option_08)
              .tag == None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____5 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)168U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c61(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_c63(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_c6(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[1U];
  /* generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out); or */
  memcpy(copy_of_data, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_9e4(copy_of_data, out);
}

/**
 A portable SHAKE128 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_shake128(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_c6(buf0, buf);
}

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
static KRML_MUSTINLINE void libcrux_sha3_shake128_ema(Eurydice_slice out,
                                                      Eurydice_slice data) {
  libcrux_sha3_portable_shake128(out, data);
}

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
static KRML_MUSTINLINE void libcrux_sha3_shake256_ema(Eurydice_slice out,
                                                      Eurydice_slice data) {
  libcrux_sha3_portable_shake256(out, data);
}

static const size_t libcrux_sha3_generic_keccak__PI[24U] = {
    (size_t)6U, (size_t)12U, (size_t)18U, (size_t)24U, (size_t)3U,
    (size_t)9U, (size_t)10U, (size_t)16U, (size_t)22U, (size_t)1U,
    (size_t)7U, (size_t)13U, (size_t)19U, (size_t)20U, (size_t)4U,
    (size_t)5U, (size_t)11U, (size_t)17U, (size_t)23U, (size_t)2U,
    (size_t)8U, (size_t)14U, (size_t)15U, (size_t)21U};

static const size_t libcrux_sha3_generic_keccak__ROTC[24U] = {
    (size_t)1U,  (size_t)62U, (size_t)28U, (size_t)27U, (size_t)36U,
    (size_t)44U, (size_t)6U,  (size_t)55U, (size_t)20U, (size_t)3U,
    (size_t)10U, (size_t)43U, (size_t)25U, (size_t)39U, (size_t)41U,
    (size_t)45U, (size_t)15U, (size_t)21U, (size_t)8U,  (size_t)18U,
    (size_t)2U,  (size_t)61U, (size_t)56U, (size_t)14U};

/**
 A portable SHA3 224 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 A portable SHA3 256 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_sha256(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 A portable SHA3 384 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 A portable SHA3 512 implementation.
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_sha512(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0,
                                                          Eurydice_slice input1,
                                                          Eurydice_slice out0,
                                                          Eurydice_slice out1) {
  /* TODO: make argument ordering consistent */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

typedef struct libcrux_sha3_neon_x2_incremental_KeccakState_s {
  libcrux_sha3_generic_keccak_KeccakState_17 state[2U];
} libcrux_sha3_neon_x2_incremental_KeccakState;

/**
 Initialise the `KeccakState2`.
*/
static KRML_MUSTINLINE libcrux_sha3_neon_x2_incremental_KeccakState
libcrux_sha3_neon_x2_incremental_init(void) {
  /* XXX: These functions could alternatively implement the same with the
   * portable implementation { let s0 = KeccakState::new(); let s1 =
   * KeccakState::new(); [s0, s1] } */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1) {
  /* XXX: These functions could alternatively implement the same with the
   * portable implementation { let [mut s0, mut s1] = s;
   * shake128_absorb_final(&mut s0, data0); shake128_absorb_final(&mut s1,
   * data1); } */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  /* XXX: These functions could alternatively implement the same with the
   * portable implementation { let [mut s0, mut s1] = s;
   * shake128_squeeze_first_three_blocks(&mut s0, out0);
   * shake128_squeeze_first_three_blocks(&mut s1, out1); } */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  /* XXX: These functions could alternatively implement the same with the
   * portable implementation { let [mut s0, mut s1] = s;
   * shake128_squeeze_next_block(&mut s0, out0);
   * shake128_squeeze_next_block(&mut s1, out1); } */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze five blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Shake256 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_absorb_final(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1) {
  /* XXX: These functions could alternatively implement the same with the
   * portable implementation { let [mut s0, mut s1] = s;
   * shake128_absorb_final(&mut s0, data0); shake128_absorb_final(&mut s1,
   * data1); } */
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze block
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_first_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Squeeze next block
*/
static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_next_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_c61(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o1);
  Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o2);
  Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_c61(s, o4);
}

/**
 Squeeze five blocks
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_c6(s, buf);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_9e1(s, buf);
}

/**
 Create a new SHAKE-256 state object.
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_89_04();
}

/**
 Squeeze the first SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block_c60(s, buf);
}

/**
 Squeeze the next SHAKE-256 block
*/
static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block_c60(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_e2_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_e2;

typedef libcrux_sha3_generic_keccak_KeccakXofState_e2
    libcrux_sha3_portable_incremental_Shake256Absorb;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (
        /* There's something buffered internally to consume. */ self->buf_len +
            input_len >=
        (size_t)136U) {
      consumed = (size_t)136U - /* We have enough data when combining the
                                   internal buffer and the input. */
                 self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)136U, self->buf[i0], self->buf_len, uint8_t, size_t);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_8b_c6(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      uint8_t buf[136U] = {0U};
      borrowed[i] = core_array___Array_T__N__23__as_slice(
          (size_t)136U, buf, uint8_t, Eurydice_slice);
    }
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      borrowed[i0] =
          Eurydice_array_to_slice((size_t)136U, self->buf[i0], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_5b(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_inputs[1U];
    memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(
        copy_of_inputs, input_consumed + i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_portable_keccak_load_block_5a_5b(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c6(uu____0, copy_of_inputs);
  if (
      /* ... buffer the rest if there's not enough input (left). */
      input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          self->buf[i0], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____2,
          Eurydice_slice_subslice_from(
              inputs[i0], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
 Shake256 absorb
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline void libcrux_sha3_portable_incremental_absorb_7d(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_8b_c6(self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState_e2
    libcrux_sha3_portable_incremental_Shake256Squeeze;

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_8b_9e(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c6(uu____0, copy_of_inputs);
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, self->buf_len, uint8_t);
      Eurydice_slice_copy(uu____2,
                          Eurydice_array_to_subslice2(self->buf[i0], (size_t)0U,
                                                      self->buf_len, uint8_t),
                          uint8_t);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
          blocks[i0], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____3,
          Eurydice_slice_subslice_from(
              inputs[i0], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    blocks[i0][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i0;
    size_t uu____5 = (size_t)136U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
}

/**
 Shake256 absorb final
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_e2
libcrux_sha3_portable_incremental_absorb_final_7d(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_8b_9e(&self, buf);
  return self;
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline void libcrux_sha3_generic_keccak_zero_block_8b_c6(
    uint8_t ret[136U]) {
  ret[0U] = 0U;
  ret[1U] = 0U;
  ret[2U] = 0U;
  ret[3U] = 0U;
  ret[4U] = 0U;
  ret[5U] = 0U;
  ret[6U] = 0U;
  ret[7U] = 0U;
  ret[8U] = 0U;
  ret[9U] = 0U;
  ret[10U] = 0U;
  ret[11U] = 0U;
  ret[12U] = 0U;
  ret[13U] = 0U;
  ret[14U] = 0U;
  ret[15U] = 0U;
  ret[16U] = 0U;
  ret[17U] = 0U;
  ret[18U] = 0U;
  ret[19U] = 0U;
  ret[20U] = 0U;
  ret[21U] = 0U;
  ret[22U] = 0U;
  ret[23U] = 0U;
  ret[24U] = 0U;
  ret[25U] = 0U;
  ret[26U] = 0U;
  ret[27U] = 0U;
  ret[28U] = 0U;
  ret[29U] = 0U;
  ret[30U] = 0U;
  ret[31U] = 0U;
  ret[32U] = 0U;
  ret[33U] = 0U;
  ret[34U] = 0U;
  ret[35U] = 0U;
  ret[36U] = 0U;
  ret[37U] = 0U;
  ret[38U] = 0U;
  ret[39U] = 0U;
  ret[40U] = 0U;
  ret[41U] = 0U;
  ret[42U] = 0U;
  ret[43U] = 0U;
  ret[44U] = 0U;
  ret[45U] = 0U;
  ret[46U] = 0U;
  ret[47U] = 0U;
  ret[48U] = 0U;
  ret[49U] = 0U;
  ret[50U] = 0U;
  ret[51U] = 0U;
  ret[52U] = 0U;
  ret[53U] = 0U;
  ret[54U] = 0U;
  ret[55U] = 0U;
  ret[56U] = 0U;
  ret[57U] = 0U;
  ret[58U] = 0U;
  ret[59U] = 0U;
  ret[60U] = 0U;
  ret[61U] = 0U;
  ret[62U] = 0U;
  ret[63U] = 0U;
  ret[64U] = 0U;
  ret[65U] = 0U;
  ret[66U] = 0U;
  ret[67U] = 0U;
  ret[68U] = 0U;
  ret[69U] = 0U;
  ret[70U] = 0U;
  ret[71U] = 0U;
  ret[72U] = 0U;
  ret[73U] = 0U;
  ret[74U] = 0U;
  ret[75U] = 0U;
  ret[76U] = 0U;
  ret[77U] = 0U;
  ret[78U] = 0U;
  ret[79U] = 0U;
  ret[80U] = 0U;
  ret[81U] = 0U;
  ret[82U] = 0U;
  ret[83U] = 0U;
  ret[84U] = 0U;
  ret[85U] = 0U;
  ret[86U] = 0U;
  ret[87U] = 0U;
  ret[88U] = 0U;
  ret[89U] = 0U;
  ret[90U] = 0U;
  ret[91U] = 0U;
  ret[92U] = 0U;
  ret[93U] = 0U;
  ret[94U] = 0U;
  ret[95U] = 0U;
  ret[96U] = 0U;
  ret[97U] = 0U;
  ret[98U] = 0U;
  ret[99U] = 0U;
  ret[100U] = 0U;
  ret[101U] = 0U;
  ret[102U] = 0U;
  ret[103U] = 0U;
  ret[104U] = 0U;
  ret[105U] = 0U;
  ret[106U] = 0U;
  ret[107U] = 0U;
  ret[108U] = 0U;
  ret[109U] = 0U;
  ret[110U] = 0U;
  ret[111U] = 0U;
  ret[112U] = 0U;
  ret[113U] = 0U;
  ret[114U] = 0U;
  ret[115U] = 0U;
  ret[116U] = 0U;
  ret[117U] = 0U;
  ret[118U] = 0U;
  ret[119U] = 0U;
  ret[120U] = 0U;
  ret[121U] = 0U;
  ret[122U] = 0U;
  ret[123U] = 0U;
  ret[124U] = 0U;
  ret[125U] = 0U;
  ret[126U] = 0U;
  ret[127U] = 0U;
  ret[128U] = 0U;
  ret[129U] = 0U;
  ret[130U] = 0U;
  ret[131U] = 0U;
  ret[132U] = 0U;
  ret[133U] = 0U;
  ret[134U] = 0U;
  ret[135U] = 0U;
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_e2
libcrux_sha3_generic_keccak_new_8b_c6(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_e2 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_89_04();
  uint8_t ret[136U];
  libcrux_sha3_generic_keccak_zero_block_8b_c6(ret);
  memcpy(lit.buf[0U], ret, (size_t)136U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
 Shake256 new state
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<136: usize> for
libcrux_sha3::portable::incremental::Shake256Absorb)#2}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_e2
libcrux_sha3_portable_incremental_new_7d(void) {
  return libcrux_sha3_generic_keccak_new_8b_c6();
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakXofState_97_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState_97;

typedef libcrux_sha3_generic_keccak_KeccakXofState_97
    libcrux_sha3_portable_incremental_Shake128Absorb;

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.fill_buffer_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_fill_buffer_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (
        /* There's something buffered internally to consume. */ self->buf_len +
            input_len >=
        (size_t)168U) {
      consumed = (size_t)168U - /* We have enough data when combining the
                                   internal buffer and the input. */
                 self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)168U, self->buf[i0], self->buf_len, uint8_t, size_t);
        Eurydice_slice_copy(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t),
            uint8_t);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_full_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline size_t libcrux_sha3_generic_keccak_absorb_full_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs0[1U];
  memcpy(copy_of_inputs0, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak_fill_buffer_8b_c60(uu____0, copy_of_inputs0);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      uint8_t buf[168U] = {0U};
      borrowed[i] = core_array___Array_T__N__23__as_slice(
          (size_t)168U, buf, uint8_t, Eurydice_slice);
    }
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      borrowed[i0] =
          Eurydice_array_to_slice((size_t)168U, self->buf[i0], uint8_t);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak_load_block_5a_3a(uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      Eurydice_slice_len(inputs[0U], uint8_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_inputs[1U];
    memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak_slice_n_5a(
        copy_of_inputs, input_consumed + i0 * (size_t)168U, (size_t)168U, ret);
    libcrux_sha3_portable_keccak_load_block_5a_3a(uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c60(uu____0, copy_of_inputs);
  if (
      /* ... buffer the rest if there's not enough input (left). */
      input_remainder_len > (size_t)0U) {
    size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          self->buf[i0], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____2,
          Eurydice_slice_subslice_from(
              inputs[i0], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline void libcrux_sha3_portable_incremental_absorb_1c(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_8b_c60(self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState_97
    libcrux_sha3_portable_incremental_Shake128Squeeze;

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_8b_9e0(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 *uu____0 = self;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_inputs[1U];
  memcpy(copy_of_inputs, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak_absorb_full_8b_c60(uu____0, copy_of_inputs);
  size_t input_len = Eurydice_slice_len(inputs[0U], uint8_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, self->buf_len, uint8_t);
      Eurydice_slice_copy(uu____2,
                          Eurydice_array_to_subslice2(self->buf[i0], (size_t)0U,
                                                      self->buf_len, uint8_t),
                          uint8_t);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
          blocks[i0], self->buf_len, self->buf_len + input_remainder_len,
          uint8_t);
      Eurydice_slice_copy(
          uu____3,
          Eurydice_slice_subslice_from(
              inputs[i0], input_len - input_remainder_len, uint8_t, size_t),
          uint8_t);
    }
    blocks[i0][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i0;
    size_t uu____5 = (size_t)168U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_3a(uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
}

/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_97
libcrux_sha3_portable_incremental_absorb_final_1c(
    libcrux_sha3_generic_keccak_KeccakXofState_97 self, Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak_absorb_final_8b_9e0(&self, buf);
  return self;
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.zero_block_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline void libcrux_sha3_generic_keccak_zero_block_8b_c60(
    uint8_t ret[168U]) {
  ret[0U] = 0U;
  ret[1U] = 0U;
  ret[2U] = 0U;
  ret[3U] = 0U;
  ret[4U] = 0U;
  ret[5U] = 0U;
  ret[6U] = 0U;
  ret[7U] = 0U;
  ret[8U] = 0U;
  ret[9U] = 0U;
  ret[10U] = 0U;
  ret[11U] = 0U;
  ret[12U] = 0U;
  ret[13U] = 0U;
  ret[14U] = 0U;
  ret[15U] = 0U;
  ret[16U] = 0U;
  ret[17U] = 0U;
  ret[18U] = 0U;
  ret[19U] = 0U;
  ret[20U] = 0U;
  ret[21U] = 0U;
  ret[22U] = 0U;
  ret[23U] = 0U;
  ret[24U] = 0U;
  ret[25U] = 0U;
  ret[26U] = 0U;
  ret[27U] = 0U;
  ret[28U] = 0U;
  ret[29U] = 0U;
  ret[30U] = 0U;
  ret[31U] = 0U;
  ret[32U] = 0U;
  ret[33U] = 0U;
  ret[34U] = 0U;
  ret[35U] = 0U;
  ret[36U] = 0U;
  ret[37U] = 0U;
  ret[38U] = 0U;
  ret[39U] = 0U;
  ret[40U] = 0U;
  ret[41U] = 0U;
  ret[42U] = 0U;
  ret[43U] = 0U;
  ret[44U] = 0U;
  ret[45U] = 0U;
  ret[46U] = 0U;
  ret[47U] = 0U;
  ret[48U] = 0U;
  ret[49U] = 0U;
  ret[50U] = 0U;
  ret[51U] = 0U;
  ret[52U] = 0U;
  ret[53U] = 0U;
  ret[54U] = 0U;
  ret[55U] = 0U;
  ret[56U] = 0U;
  ret[57U] = 0U;
  ret[58U] = 0U;
  ret[59U] = 0U;
  ret[60U] = 0U;
  ret[61U] = 0U;
  ret[62U] = 0U;
  ret[63U] = 0U;
  ret[64U] = 0U;
  ret[65U] = 0U;
  ret[66U] = 0U;
  ret[67U] = 0U;
  ret[68U] = 0U;
  ret[69U] = 0U;
  ret[70U] = 0U;
  ret[71U] = 0U;
  ret[72U] = 0U;
  ret[73U] = 0U;
  ret[74U] = 0U;
  ret[75U] = 0U;
  ret[76U] = 0U;
  ret[77U] = 0U;
  ret[78U] = 0U;
  ret[79U] = 0U;
  ret[80U] = 0U;
  ret[81U] = 0U;
  ret[82U] = 0U;
  ret[83U] = 0U;
  ret[84U] = 0U;
  ret[85U] = 0U;
  ret[86U] = 0U;
  ret[87U] = 0U;
  ret[88U] = 0U;
  ret[89U] = 0U;
  ret[90U] = 0U;
  ret[91U] = 0U;
  ret[92U] = 0U;
  ret[93U] = 0U;
  ret[94U] = 0U;
  ret[95U] = 0U;
  ret[96U] = 0U;
  ret[97U] = 0U;
  ret[98U] = 0U;
  ret[99U] = 0U;
  ret[100U] = 0U;
  ret[101U] = 0U;
  ret[102U] = 0U;
  ret[103U] = 0U;
  ret[104U] = 0U;
  ret[105U] = 0U;
  ret[106U] = 0U;
  ret[107U] = 0U;
  ret[108U] = 0U;
  ret[109U] = 0U;
  ret[110U] = 0U;
  ret[111U] = 0U;
  ret[112U] = 0U;
  ret[113U] = 0U;
  ret[114U] = 0U;
  ret[115U] = 0U;
  ret[116U] = 0U;
  ret[117U] = 0U;
  ret[118U] = 0U;
  ret[119U] = 0U;
  ret[120U] = 0U;
  ret[121U] = 0U;
  ret[122U] = 0U;
  ret[123U] = 0U;
  ret[124U] = 0U;
  ret[125U] = 0U;
  ret[126U] = 0U;
  ret[127U] = 0U;
  ret[128U] = 0U;
  ret[129U] = 0U;
  ret[130U] = 0U;
  ret[131U] = 0U;
  ret[132U] = 0U;
  ret[133U] = 0U;
  ret[134U] = 0U;
  ret[135U] = 0U;
  ret[136U] = 0U;
  ret[137U] = 0U;
  ret[138U] = 0U;
  ret[139U] = 0U;
  ret[140U] = 0U;
  ret[141U] = 0U;
  ret[142U] = 0U;
  ret[143U] = 0U;
  ret[144U] = 0U;
  ret[145U] = 0U;
  ret[146U] = 0U;
  ret[147U] = 0U;
  ret[148U] = 0U;
  ret[149U] = 0U;
  ret[150U] = 0U;
  ret[151U] = 0U;
  ret[152U] = 0U;
  ret[153U] = 0U;
  ret[154U] = 0U;
  ret[155U] = 0U;
  ret[156U] = 0U;
  ret[157U] = 0U;
  ret[158U] = 0U;
  ret[159U] = 0U;
  ret[160U] = 0U;
  ret[161U] = 0U;
  ret[162U] = 0U;
  ret[163U] = 0U;
  ret[164U] = 0U;
  ret[165U] = 0U;
  ret[166U] = 0U;
  ret[167U] = 0U;
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_97
libcrux_sha3_generic_keccak_new_8b_c60(void) {
  libcrux_sha3_generic_keccak_KeccakXofState_97 lit;
  lit.inner = libcrux_sha3_generic_keccak_new_89_04();
  uint8_t ret[168U];
  libcrux_sha3_generic_keccak_zero_block_8b_c60(ret);
  memcpy(lit.buf[0U], ret, (size_t)168U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofAbsorb<168: usize> for
libcrux_sha3::portable::incremental::Shake128Absorb)}
*/
static inline libcrux_sha3_generic_keccak_KeccakXofState_97
libcrux_sha3_portable_incremental_new_1c(void) {
  return libcrux_sha3_generic_keccak_new_8b_c60();
}

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_5a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_5b(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks = Eurydice_slice_len(out[0U], uint8_t) / (size_t)8U;
  size_t last_block_len = Eurydice_slice_len(out[0U], uint8_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice2(
        out[0U], num_full_blocks * (size_t)8U,
        num_full_blocks * (size_t)8U + last_block_len, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice2(ret, (size_t)0U, last_block_len, uint8_t),
        uint8_t);
  }
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_8b_c6(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >=
      /* Squeeze out one to start with. XXX: Eurydice does not extract
         `core::cmp::min`, so we do this instead. (cf.
         https://github.com/AeneasVerif/eurydice/issues/49) */
      out_len

  ) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out00);
  core_ops_range_Range_08 iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          (CLITERAL(core_ops_range_Range_08){
              .start = (size_t)1U,
              .end = /* If we got asked for more than one block, squeeze out
                        more. */
              blocks}),
          core_ops_range_Range_08, core_ops_range_Range_08);
  while (true) {
    if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
            &iter, size_t, Option_08)
            .tag == None) {
      break;
    } else {
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(/* Here we know that we
                                                            always have full
                                                            blocks to write out.
                                                          */
                                                         out_rest,
                                                         (size_t)136U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_5b(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake256 squeeze
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofSqueeze<136: usize> for
libcrux_sha3::portable::incremental::Shake256Squeeze)#3}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_8a(
    libcrux_sha3_generic_keccak_KeccakXofState_e2 *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_8b_c6(self, buf);
}

/**
 `out` has the exact size we want here. It must be less than or equal to `RATE`.
*/
/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_5a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_5a_3a(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks = Eurydice_slice_len(out[0U], uint8_t) / (size_t)8U;
  size_t last_block_len = Eurydice_slice_len(out[0U], uint8_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out[0U], i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)8U, ret, uint8_t), uint8_t);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice2(
        out[0U], num_full_blocks * (size_t)8U,
        num_full_blocks * (size_t)8U + last_block_len, uint8_t);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    Eurydice_slice_copy(
        uu____1,
        Eurydice_array_to_subslice2(ret, (size_t)0U, last_block_len, uint8_t),
        uint8_t);
  }
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakXofState<STATE,
PARALLEL_LANES, RATE>[TraitClause@0, TraitClause@1]#2}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_8b
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_8b_c60(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
  }
  size_t out_len = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = out_len / (size_t)168U;
  size_t last = out_len - out_len % (size_t)168U;
  size_t mid;
  if ((size_t)168U >=
      /* Squeeze out one to start with. XXX: Eurydice does not extract
         `core::cmp::min`, so we do this instead. (cf.
         https://github.com/AeneasVerif/eurydice/issues/49) */
      out_len

  ) {
    mid = out_len;
  } else {
    mid = (size_t)168U;
  }
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out00);
  core_ops_range_Range_08 iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          (CLITERAL(core_ops_range_Range_08){
              .start = (size_t)1U,
              .end = /* If we got asked for more than one block, squeeze out
                        more. */
              blocks}),
          core_ops_range_Range_08, core_ops_range_Range_08);
  while (true) {
    if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
            &iter, size_t, Option_08)
            .tag == None) {
      break;
    } else {
      Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
          libcrux_sha3_portable_keccak_split_at_mut_n_5a(/* Here we know that we
                                                            always have full
                                                            blocks to write out.
                                                          */
                                                         out_rest,
                                                         (size_t)168U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
      libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600_04(&self->inner);
    libcrux_sha3_portable_keccak_store_5a_3a(self->inner.st, out_rest);
  }
  self->sponge = true;
}

/**
 Shake128 squeeze
*/
/**
This function found in impl
{(libcrux_sha3::portable::incremental::XofSqueeze<168: usize> for
libcrux_sha3::portable::incremental::Shake128Squeeze)#1}
*/
static inline void libcrux_sha3_portable_incremental_squeeze_10(
    libcrux_sha3_generic_keccak_KeccakXofState_97 *self, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_8b_c60(self, buf);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::portable::KeccakState)}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_clone_3d(
    libcrux_sha3_generic_keccak_KeccakState_17 *self) {
  return self[0U];
}

/**
This function found in impl {(core::convert::From<libcrux_sha3::Algorithm> for
u32)#1}
*/
static inline uint32_t libcrux_sha3_from_eb(libcrux_sha3_Algorithm v) {
  uint32_t uu____0;
  switch (v) {
    case libcrux_sha3_Sha224: {
      uu____0 = 1U;
      break;
    }
    case libcrux_sha3_Sha256: {
      uu____0 = 2U;
      break;
    }
    case libcrux_sha3_Sha384: {
      uu____0 = 3U;
      break;
    }
    case libcrux_sha3_Sha512: {
      uu____0 = 4U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return uu____0;
}

/**
This function found in impl {(core::convert::From<u32> for
libcrux_sha3::Algorithm)}
*/
static inline libcrux_sha3_Algorithm libcrux_sha3_from_2d(uint32_t v) {
  libcrux_sha3_Algorithm uu____0;
  switch (v) {
    case 1U: {
      uu____0 = libcrux_sha3_Sha224;
      break;
    }
    case 2U: {
      uu____0 = libcrux_sha3_Sha256;
      break;
    }
    case 3U: {
      uu____0 = libcrux_sha3_Sha384;
      break;
    }
    case 4U: {
      uu____0 = libcrux_sha3_Sha512;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  return uu____0;
}

typedef uint8_t libcrux_sha3_Sha3_512Digest[64U];

typedef uint8_t libcrux_sha3_Sha3_384Digest[48U];

typedef uint8_t libcrux_sha3_Sha3_256Digest[32U];

typedef uint8_t libcrux_sha3_Sha3_224Digest[28U];

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_portable_H_DEFINED
#endif
