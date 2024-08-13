/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
<<<<<<< HEAD
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: ab466d75991f78bb7925bf97c8ee9874f67074f5
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: b2314d1e996ac7a4fbda72210b4aabbd915d282a
=======
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 75bf8bca5f9903b4f6e8fba693d61af1415d512f
>>>>>>> main
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
libcrux_sha3_portable_keccak_rotate_left_db(uint64_t x) {
  return x << (uint32_t)(int32_t)1 | x >> (uint32_t)(int32_t)63;
}

static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vrax1q_u64(uint64_t a, uint64_t b) {
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_portable_keccak_rotate_left_db(b);
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
libcrux_sha3_generic_keccak_new_1e_f2(void) {
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
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_b3(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_fd(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_b3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db0(uint64_t x) {
  return x << (uint32_t)(int32_t)36 | x >> (uint32_t)(int32_t)28;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db0(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db1(uint64_t x) {
  return x << (uint32_t)(int32_t)3 | x >> (uint32_t)(int32_t)61;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d0(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db1(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da0(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db2(uint64_t x) {
  return x << (uint32_t)(int32_t)41 | x >> (uint32_t)(int32_t)23;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d1(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db2(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da1(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db3(uint64_t x) {
  return x << (uint32_t)(int32_t)18 | x >> (uint32_t)(int32_t)46;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d2(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db3(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da2(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d3(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da3(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d3(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db4(uint64_t x) {
  return x << (uint32_t)(int32_t)44 | x >> (uint32_t)(int32_t)20;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d4(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db4(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da4(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d4(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db5(uint64_t x) {
  return x << (uint32_t)(int32_t)10 | x >> (uint32_t)(int32_t)54;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d5(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db5(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da5(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d5(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db6(uint64_t x) {
  return x << (uint32_t)(int32_t)45 | x >> (uint32_t)(int32_t)19;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d6(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db6(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da6(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d6(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db7(uint64_t x) {
  return x << (uint32_t)(int32_t)2 | x >> (uint32_t)(int32_t)62;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d7(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db7(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da7(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d7(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db8(uint64_t x) {
  return x << (uint32_t)(int32_t)62 | x >> (uint32_t)(int32_t)2;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d8(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db8(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da8(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d8(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db9(uint64_t x) {
  return x << (uint32_t)(int32_t)6 | x >> (uint32_t)(int32_t)58;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d9(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db9(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da9(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db10(uint64_t x) {
  return x << (uint32_t)(int32_t)43 | x >> (uint32_t)(int32_t)21;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d10(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db10(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da10(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db11(uint64_t x) {
  return x << (uint32_t)(int32_t)15 | x >> (uint32_t)(int32_t)49;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d11(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db11(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da11(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db12(uint64_t x) {
  return x << (uint32_t)(int32_t)61 | x >> (uint32_t)(int32_t)3;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d12(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db12(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da12(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db13(uint64_t x) {
  return x << (uint32_t)(int32_t)28 | x >> (uint32_t)(int32_t)36;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d13(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db13(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da13(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db14(uint64_t x) {
  return x << (uint32_t)(int32_t)55 | x >> (uint32_t)(int32_t)9;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d14(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db14(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da14(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db15(uint64_t x) {
  return x << (uint32_t)(int32_t)25 | x >> (uint32_t)(int32_t)39;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d15(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db15(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da15(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db16(uint64_t x) {
  return x << (uint32_t)(int32_t)21 | x >> (uint32_t)(int32_t)43;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d16(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db16(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da16(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db17(uint64_t x) {
  return x << (uint32_t)(int32_t)56 | x >> (uint32_t)(int32_t)8;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d17(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db17(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da17(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db18(uint64_t x) {
  return x << (uint32_t)(int32_t)27 | x >> (uint32_t)(int32_t)37;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d18(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db18(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da18(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db19(uint64_t x) {
  return x << (uint32_t)(int32_t)20 | x >> (uint32_t)(int32_t)44;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d19(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db19(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da19(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db20(uint64_t x) {
  return x << (uint32_t)(int32_t)39 | x >> (uint32_t)(int32_t)25;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d20(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db20(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da20(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d20(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db21(uint64_t x) {
  return x << (uint32_t)(int32_t)8 | x >> (uint32_t)(int32_t)56;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d21(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db21(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da21(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d21(a, b);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak_rotate_left_db22(uint64_t x) {
  return x << (uint32_t)(int32_t)14 | x >> (uint32_t)(int32_t)50;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64_t
libcrux_sha3_portable_keccak__vxarq_u64_3d22(uint64_t a, uint64_t b) {
  uint64_t ab = a ^ b;
  return libcrux_sha3_portable_keccak_rotate_left_db22(ab);
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
libcrux_sha3_portable_keccak_xor_and_rotate_5a_da22(uint64_t a, uint64_t b) {
  return libcrux_sha3_portable_keccak__vxarq_u64_3d22(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_eb(
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
  uint64_t uu____4 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da(s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  uint64_t uu____5 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da0(s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  uint64_t uu____6 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da1(s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  uint64_t uu____7 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da2(s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  uint64_t uu____8 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da3(s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  uint64_t uu____9 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da4(s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  uint64_t uu____10 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da5(s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  uint64_t uu____11 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da6(s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  uint64_t uu____12 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da7(s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  uint64_t uu____13 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da8(s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  uint64_t uu____14 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da9(s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  uint64_t uu____15 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da10(s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  uint64_t uu____16 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da11(s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  uint64_t uu____17 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da12(s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  uint64_t uu____18 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da13(s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  uint64_t uu____19 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da14(s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  uint64_t uu____20 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da15(s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  uint64_t uu____21 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da16(s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  uint64_t uu____22 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da17(s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  uint64_t uu____23 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da18(s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  uint64_t uu____24 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da19(s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  uint64_t uu____25 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da20(s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  uint64_t uu____26 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da21(s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
  uint64_t uu____27 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_da22(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types uint64_t
with const generics
- N= 1
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_b8(
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_1f(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_83(
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_85(
    libcrux_sha3_generic_keccak_KeccakState_48 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_eb(s);
    libcrux_sha3_generic_keccak_pi_b8(s);
    libcrux_sha3_generic_keccak_chi_1f(s);
    libcrux_sha3_generic_keccak_iota_83(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_75(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_fd(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_b3(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_71(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_72(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)72U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_71(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_58(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_fa(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_58(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5a_78(
    uint64_t (*a)[5U], uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_fa(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5d(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_78(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_6f(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_09(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_6f(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1f(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
  libcrux_sha3_portable_keccak_store_block_5a_6f(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_83(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_78(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_75(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_75(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_72(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)72U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_09(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_83(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_75(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha512(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_b30(
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_fd0(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_b30(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_750(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_fd0(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a0(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_b30(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_710(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_720(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_710(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_580(
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
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_fa0(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_580(s, buf);
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
libcrux_sha3_portable_keccak_store_block_full_5a_780(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_fa0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5d0(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_780(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_6f0(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_580(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_090(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_6f0(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1f0(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
  libcrux_sha3_portable_keccak_store_block_5a_6f0(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_830(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_780(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_750(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_750(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_720(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d0(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_090(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f0(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_830(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_750(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha256(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a0(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_721(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_710(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_751(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_750(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_721(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d0(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_090(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f0(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_830(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a1(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_751(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_shake256(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a1(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha512(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha256(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0,
                                                          Eurydice_slice input1,
                                                          Eurydice_slice out0,
                                                          Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

typedef libcrux_sha3_generic_keccak_KeccakState_48
    libcrux_sha3_portable_KeccakState;

typedef struct libcrux_sha3_neon_x2_incremental_KeccakState_s {
  libcrux_sha3_generic_keccak_KeccakState_48 state[2U];
} libcrux_sha3_neon_x2_incremental_KeccakState;

static KRML_MUSTINLINE libcrux_sha3_neon_x2_incremental_KeccakState
libcrux_sha3_neon_x2_incremental_shake128_init(void) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice data0,
    Eurydice_slice data1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_neon_x2_incremental_KeccakState *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_f2();
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_b31(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a1(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_b31(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_711(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a1(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_722(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_711(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_722(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_581(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_6f1(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_581(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1f1(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
  libcrux_sha3_portable_keccak_store_block_5a_6f1(s->st, out);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_091(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_6f1(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_7d(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_091(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o2);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_7d(s, buf);
}

#define libcrux_sha3_Sha224 0
#define libcrux_sha3_Sha256 1
#define libcrux_sha3_Sha384 2
#define libcrux_sha3_Sha512 3

typedef uint8_t libcrux_sha3_Algorithm;

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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_b32(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_fd1(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_b32(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_751(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_fd1(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a2(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_b32(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_712(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_723(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)144U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_712(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_582(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_fa1(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_582(s, buf);
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
libcrux_sha3_portable_keccak_store_block_full_5a_781(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_fa1(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5d1(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_781(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_6f2(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_582(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_092(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_6f2(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1f2(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
  libcrux_sha3_portable_keccak_store_block_5a_6f2(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_831(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_781(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_752(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_751(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_723(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d1(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)144U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_092(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f2(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_831(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a2(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_752(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a2(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_b33(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_fd2(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_b33(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_752(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_fd2(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a3(
    uint64_t (*s)[5U], uint8_t blocks[1U][200U]) {
  Eurydice_slice buf[1U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_load_block_b33(s, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_713(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_7a3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_724(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice last[1U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (last_len > (size_t)0U) {
      Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
          blocks[i0], (size_t)0U, last_len, uint8_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(uu____0, last[i0], uint8_t,
                                             void *);
    }
    blocks[i0][last_len] = 6U;
    size_t uu____1 = i0;
    size_t uu____2 = (size_t)104U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  uint64_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[1U][200U];
  memcpy(uu____4, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_5a_713(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_583(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_fa2(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_583(s, buf);
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
libcrux_sha3_portable_keccak_store_block_full_5a_782(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_fa2(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5d2(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_782(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_5a
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_6f3(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_583(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_093(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_6f3(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_1f3(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
  libcrux_sha3_portable_keccak_store_block_5a_6f3(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_832(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_782(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_753(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_752(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_724(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d2(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)104U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_093(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f3(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_832(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a3(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_753(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a3(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_sha224_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha224(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha224(Eurydice_slice data,
                                                uint8_t ret[28U]) {
  uint8_t out[28U] = {0U};
  libcrux_sha3_sha224_ema(
      Eurydice_array_to_slice((size_t)28U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)28U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha256_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha256(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha256(Eurydice_slice data,
                                                uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  libcrux_sha3_sha256_ema(
      Eurydice_array_to_slice((size_t)32U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha384_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha384(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha384(Eurydice_slice data,
                                                uint8_t ret[48U]) {
  uint8_t out[48U] = {0U};
  libcrux_sha3_sha384_ema(
      Eurydice_array_to_slice((size_t)48U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)48U * sizeof(uint8_t));
}

static KRML_MUSTINLINE void libcrux_sha3_sha512_ema(Eurydice_slice digest,
                                                    Eurydice_slice payload) {
  libcrux_sha3_portable_sha512(digest, payload);
}

static KRML_MUSTINLINE void libcrux_sha3_sha512(Eurydice_slice data,
                                                uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  libcrux_sha3_sha512_ema(
      Eurydice_array_to_slice((size_t)64U, out, uint8_t, Eurydice_slice), data);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_fd3(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  uint64_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, b, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_b31(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_753(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice blocks[1U]) {
  uint64_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, blocks, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak_load_block_5a_fd3(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_85(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_fa3(
    uint64_t (*s)[5U], uint8_t ret[1U][200U]) {
  uint8_t out[200U] = {0U};
  Eurydice_slice buf[1U] = {
      Eurydice_array_to_slice((size_t)200U, out, uint8_t, Eurydice_slice)};
  libcrux_sha3_portable_keccak_store_block_581(s, buf);
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
libcrux_sha3_portable_keccak_store_block_full_5a_783(uint64_t (*a)[5U],
                                                     uint8_t ret[1U][200U]) {
  libcrux_sha3_portable_keccak_store_block_full_fa3(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_5d3(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_783(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_833(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_85(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_783(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
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
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_754(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_48 s =
      libcrux_sha3_generic_keccak_new_1e_f2();
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
    libcrux_sha3_generic_keccak_absorb_block_753(uu____0, ret);
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
  libcrux_sha3_generic_keccak_absorb_final_722(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_5d3(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____4 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____4.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____4.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_091(&s, o0);
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
        libcrux_sha3_generic_keccak_squeeze_next_block_1f1(&s, o);
        memcpy(o1, orest, (size_t)1U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_833(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.portable.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_2a4(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_754(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_shake128(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_2a4(buf0, buf);
}

static KRML_MUSTINLINE void libcrux_sha3_shake128_ema(Eurydice_slice out,
                                                      Eurydice_slice data) {
  libcrux_sha3_portable_shake128(out, data);
}

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

static KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest,
                                                     Eurydice_slice data) {
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
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_92(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_091(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o1);
  Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o2);
  Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_1f1(s, o4);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_92(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_721(s, buf);
}

static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_f2();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block_090(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block_1f0(s, buf);
}

<<<<<<< HEAD
typedef struct
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t_s {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t;

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
    libcrux_sha3_portable_incremental_Shake256Absorb;

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)136U) {
      consumed = (size_t)136U - self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)136U, self->buf[i0], self->buf_len, uint8_t, size_t,
            Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t,
                                       Eurydice_slice),
            uint8_t, void *);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

static inline Eurydice_slice
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full_closure__uint64_t_1size_t_136size_t(
    uint8_t (**state)[136U], size_t i) {
  return Eurydice_array_to_slice((size_t)136U, state[0U][i], uint8_t,
                                 Eurydice_slice);
}

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      borrowed[i] = Eurydice_array_to_slice((size_t)136U, self->buf[i], uint8_t,
                                            Eurydice_slice);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___136size_t(
        uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      core_slice___Slice_T___len(inputs[0U], uint8_t, size_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    Eurydice_slice uu____5[1U];
    memcpy(uu____5, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____5, input_consumed + i0 * (size_t)136U, (size_t)136U, ret);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___136size_t(
        uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  return remainder;
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)136U, self->buf[i0],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_slice_subslice_from(inputs[i0],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__absorb(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_136size_t(
      self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
    libcrux_sha3_portable_incremental_Shake256Squeeze;

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_136size_t_31uint8_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_136size_t(
          uu____0, uu____1);
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i0],
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = self->buf_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_array_to_subslice(
              (size_t)136U, self->buf[i0],
              (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                      .end = self->buf_len}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
          uint8_t, void *);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i0],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____3,
          Eurydice_slice_subslice_from(inputs[i0],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    blocks[i0][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i0;
    size_t uu____5 = (size_t)136U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full___136size_t(
      uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__absorb_final(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_136size_t_31uint8_t(
      &self, buf);
  return self;
}

static inline void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_136size_t(
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

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_136size_t(
    void) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t lit;
  lit.inner =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
  uint8_t ret[136U];
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_136size_t(
      ret);
  memcpy(lit.buf[0U], ret, (size_t)136U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_136__usize__for_libcrux_sha3__portable__incremental__Shake256Absorb__2__new(
    void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_136size_t();
}

typedef struct
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t_s {
  libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t;

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
    libcrux_sha3_portable_incremental_Shake128Absorb;

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (self->buf_len + input_len >= (size_t)168U) {
      consumed = (size_t)168U - self->buf_len;
      for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
        size_t i0 = i;
        Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
            (size_t)168U, self->buf[i0], self->buf_len, uint8_t, size_t,
            Eurydice_slice);
        core_slice___Slice_T___copy_from_slice(
            uu____0,
            Eurydice_slice_subslice_to(inputs[i0], consumed, uint8_t, size_t,
                                       Eurydice_slice),
            uint8_t, void *);
      }
      self->buf_len = self->buf_len + consumed;
    }
  }
  return consumed;
}

static inline Eurydice_slice
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full_closure__uint64_t_1size_t_168size_t(
    uint8_t (**state)[168U], size_t i) {
  return Eurydice_array_to_slice((size_t)168U, state[0U][i], uint8_t,
                                 Eurydice_slice);
}

static inline size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_consumed =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__fill_buffer__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  if (input_consumed > (size_t)0U) {
    Eurydice_slice borrowed[1U];
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      borrowed[i] = Eurydice_array_to_slice((size_t)168U, self->buf[i], uint8_t,
                                            Eurydice_slice);
    }
    uint64_t(*uu____2)[5U] = self->inner.st;
    Eurydice_slice uu____3[1U];
    memcpy(uu____3, borrowed, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___168size_t(
        uu____2, uu____3);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume =
      core_slice___Slice_T___len(inputs[0U], uint8_t, size_t) - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    uint64_t(*uu____4)[5U] = self->inner.st;
    Eurydice_slice uu____5[1U];
    memcpy(uu____5, inputs, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice ret[1U];
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___slice_n(
        uu____5, input_consumed + i0 * (size_t)168U, (size_t)168U, ret);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block___168size_t(
        uu____4, ret);
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  return remainder;
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
    for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
      size_t i0 = i;
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)168U, self->buf[i0],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_slice_subslice_from(inputs[i0],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    self->buf_len = self->buf_len + input_remainder_len;
  }
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___absorb(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb__uint64_t_1size_t_168size_t(
      self, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
    libcrux_sha3_portable_incremental_Shake128Squeeze;

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_168size_t_31uint8_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice inputs[1U]) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
      *uu____0 = self;
  Eurydice_slice uu____1[1U];
  memcpy(uu____1, inputs, (size_t)1U * sizeof(Eurydice_slice));
  size_t input_remainder_len =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_full__uint64_t_1size_t_168size_t(
          uu____0, uu____1);
  size_t input_len = core_slice___Slice_T___len(inputs[0U], uint8_t, size_t);
  uint8_t blocks[1U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (self->buf_len > (size_t)0U) {
      Eurydice_slice uu____2 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i0],
          (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                  .end = self->buf_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____2,
          Eurydice_array_to_subslice(
              (size_t)168U, self->buf[i0],
              (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                      .end = self->buf_len}),
              uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
          uint8_t, void *);
    }
    if (input_remainder_len > (size_t)0U) {
      Eurydice_slice uu____3 = Eurydice_array_to_subslice(
          (size_t)200U, blocks[i0],
          (CLITERAL(core_ops_range_Range__size_t){
              .start = self->buf_len,
              .end = self->buf_len + input_remainder_len}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
      core_slice___Slice_T___copy_from_slice(
          uu____3,
          Eurydice_slice_subslice_from(inputs[i0],
                                       input_len - input_remainder_len, uint8_t,
                                       size_t, Eurydice_slice),
          uint8_t, void *);
    }
    blocks[i0][self->buf_len + input_remainder_len] = 31U;
    size_t uu____4 = i0;
    size_t uu____5 = (size_t)168U - (size_t)1U;
    blocks[uu____4][uu____5] = (uint32_t)blocks[uu____4][uu____5] | 128U;
  }
  uint64_t(*uu____6)[5U] = self->inner.st;
  uint8_t uu____7[1U][200U];
  memcpy(uu____7, blocks, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___load_block_full___168size_t(
      uu____6, uu____7);
  libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___absorb_final(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        self,
    Eurydice_slice input) {
  Eurydice_slice buf[1U] = {input};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__absorb_final__uint64_t_1size_t_168size_t_31uint8_t(
      &self, buf);
  return self;
}

static inline void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_168size_t(
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

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_168size_t(
    void) {
  libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t lit;
  lit.inner =
      libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakState_T__N__TraitClause_0__1__new__uint64_t_1size_t();
  uint8_t ret[168U];
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__zero_block__uint64_t_1size_t_168size_t(
      ret);
  memcpy(lit.buf[0U], ret, (size_t)168U * sizeof(uint8_t));
  lit.buf_len = (size_t)0U;
  lit.sponge = false;
  return lit;
}

static inline libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofAbsorb_168__usize__for_libcrux_sha3__portable__incremental__Shake128Absorb___new(
    void) {
  return libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__new__uint64_t_1size_t_168size_t();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) / (size_t)8U;
  size_t last_block_len =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = num_full_blocks * (size_t)8U,
            .end = num_full_blocks * (size_t)8U + last_block_len}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice(
            (size_t)8U, ret,
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                    .end = last_block_len}),
            uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_136size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  size_t out_len = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
      self->inner.st, out00);
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
      K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
          libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
              out_rest, (size_t)136U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
          self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___136size_t(
        self->inner.st, out_rest);
  }
  self->sponge = true;
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofSqueeze_136__usize__for_libcrux_sha3__portable__incremental__Shake256Squeeze__3__squeeze(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__136size_t
        *self,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_136size_t(
      self, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
    uint64_t (*state)[5U], Eurydice_slice out[1U]) {
  size_t num_full_blocks =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) / (size_t)8U;
  size_t last_block_len =
      core_slice___Slice_T___len(out[0U], uint8_t, size_t) % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(state[i0 / (size_t)5U][i0 % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_slice((size_t)8U, ret, uint8_t, Eurydice_slice),
        uint8_t, void *);
  }
  if (last_block_len != (size_t)0U) {
    Eurydice_slice uu____1 = Eurydice_slice_subslice(
        out[0U],
        (CLITERAL(core_ops_range_Range__size_t){
            .start = num_full_blocks * (size_t)8U,
            .end = num_full_blocks * (size_t)8U + last_block_len}),
        uint8_t, core_ops_range_Range__size_t, Eurydice_slice);
    uint8_t ret[8U];
    core_num__u64_9__to_le_bytes(
        state[num_full_blocks / (size_t)5U][num_full_blocks % (size_t)5U], ret);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice(
            (size_t)8U, ret,
            (CLITERAL(core_ops_range_Range__size_t){.start = (size_t)0U,
                                                    .end = last_block_len}),
            uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
        uint8_t, void *);
  }
}

static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_168size_t(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice out[1U]) {
  if (self->sponge) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
  }
  size_t out_len = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = out_len / (size_t)168U;
  size_t last = out_len - out_len % (size_t)168U;
  size_t mid;
  if ((size_t)168U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)168U;
  }
  K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____0 =
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
          out, mid);
  Eurydice_slice out00[1U];
  memcpy(out00, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice out_rest[1U];
  memcpy(out_rest, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
      self->inner.st, out00);
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
      K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_ uu____1 =
          libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___split_at_mut_n(
              out_rest, (size_t)168U);
      Eurydice_slice out0[1U];
      memcpy(out0, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
      Eurydice_slice tmp[1U];
      memcpy(tmp, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
      libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
      libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
          self->inner.st, out0);
      memcpy(out_rest, tmp, (size_t)1U * sizeof(Eurydice_slice));
    }
  }
  if (last < out_len) {
    libcrux_sha3_generic_keccak_keccakf1600__uint64_t_1size_t(&self->inner);
    libcrux_sha3_portable_keccak___libcrux_sha3__traits__internal__KeccakItem_1__usize__for_u64___store___168size_t(
        self->inner.st, out_rest);
  }
  self->sponge = true;
}

static inline void
libcrux_sha3_portable_incremental___libcrux_sha3__portable__incremental__XofSqueeze_168__usize__for_libcrux_sha3__portable__incremental__Shake128Squeeze__1__squeeze(
    libcrux_sha3_generic_keccak_KeccakXofState__uint64_t__1size_t__168size_t
        *self,
    Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak__libcrux_sha3__generic_keccak__KeccakXofState_STATE__PARALLEL_LANES__RATE__TraitClause_0__2__squeeze__uint64_t_1size_t_168size_t(
      self, buf);
}

static inline libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t
libcrux_sha3_portable___core__clone__Clone_for_libcrux_sha3__portable__KeccakState___clone(
    libcrux_sha3_generic_keccak_KeccakState__uint64_t__1size_t *self) {
=======
/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::portable::KeccakState)}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_clone_3d(
    libcrux_sha3_generic_keccak_KeccakState_48 *self) {
>>>>>>> main
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
