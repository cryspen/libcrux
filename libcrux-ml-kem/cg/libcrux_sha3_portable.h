/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: 23480eeb26f8e66cfa9bd0eb76c65d87fbb91806
 */

#ifndef __libcrux_sha3_portable_H
#define __libcrux_sha3_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3_libcrux_ml_kem.h"

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
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de(
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
  libcrux_sha3_portable_keccak_load_block_de(uu____0, uu____1);
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
  uint64_t uu____4 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_65(s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  uint64_t uu____5 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_650(s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  uint64_t uu____6 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_651(s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  uint64_t uu____7 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_652(s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  uint64_t uu____8 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_653(s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  uint64_t uu____9 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_654(s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  uint64_t uu____10 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_655(s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  uint64_t uu____11 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_656(s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  uint64_t uu____12 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_657(s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  uint64_t uu____13 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_658(s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  uint64_t uu____14 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_659(s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  uint64_t uu____15 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6510(s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  uint64_t uu____16 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6511(s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  uint64_t uu____17 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6512(s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  uint64_t uu____18 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6513(s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  uint64_t uu____19 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6514(s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  uint64_t uu____20 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6515(s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  uint64_t uu____21 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6516(s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  uint64_t uu____22 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6517(s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  uint64_t uu____23 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6518(s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  uint64_t uu____24 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6519(s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  uint64_t uu____25 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6520(s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  uint64_t uu____26 =
      libcrux_sha3_portable_keccak_xor_and_rotate_5a_6521(s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
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
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5a_2d(
    uint64_t (*a)[5U], uint8_t b[1U][200U]) {
  uint64_t(*uu____0)[5U] = a;
  uint8_t uu____1[1U][200U];
  memcpy(uu____1, b, (size_t)1U * sizeof(uint8_t[200U]));
  libcrux_sha3_portable_keccak_load_block_full_ac(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_25(
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_39(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_48(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_39(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_58(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_portable_keccak_store_block_5a_48(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c8(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_48(s->st, out);
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
  libcrux_sha3_generic_keccak_absorb_final_25(uu____2, ret);
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
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)72U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c8(&s, o);
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

static KRML_MUSTINLINE void libcrux_sha3_portable_sha512(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd(buf0, buf);
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
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_250(
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
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccakx1_fd0(
    Eurydice_slice data[1U], Eurydice_slice out[1U]) {
  Eurydice_slice uu____0[1U];
  memcpy(uu____0, data, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_cf0(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_portable_sha256(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd0(buf0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_251(
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d0(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
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
  libcrux_sha3_generic_keccak_absorb_final_251(uu____2, ret);
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

static KRML_MUSTINLINE void libcrux_sha3_portable_shake256(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd1(buf0, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_zero_fa(void) {
  return libcrux_intrinsics_arm64__vdupq_n_u64(0ULL);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__veor5q_u64(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b,
    core_core_arch_arm_shared_neon_uint64x2_t c,
    core_core_arch_arm_shared_neon_uint64x2_t d,
    core_core_arch_arm_shared_neon_uint64x2_t e) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  core_core_arch_arm_shared_neon_uint64x2_t cd =
      libcrux_intrinsics_arm64__veorq_u64(c, d);
  core_core_arch_arm_shared_neon_uint64x2_t abcd =
      libcrux_intrinsics_arm64__veorq_u64(ab, cd);
  return libcrux_intrinsics_arm64__veorq_u64(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor5_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
                                core_core_arch_arm_shared_neon_uint64x2_t b,
                                core_core_arch_arm_shared_neon_uint64x2_t c,
                                core_core_arch_arm_shared_neon_uint64x2_t d,
                                core_core_arch_arm_shared_neon_uint64x2_t e) {
  return libcrux_sha3_simd_arm64__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_58(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)1, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)63, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vrax1q_u64(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t uu____0 = a;
  return libcrux_intrinsics_arm64__veorq_u64(
      uu____0, libcrux_sha3_simd_arm64_rotate_left_58(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vrax1q_u64(a, b);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vbcaxq_u64(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b,
    core_core_arch_arm_shared_neon_uint64x2_t c) {
  return libcrux_intrinsics_arm64__veorq_u64(
      a, libcrux_intrinsics_arm64__vbicq_u64(b, c));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_and_not_xor_fa(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b,
    core_core_arch_arm_shared_neon_uint64x2_t c) {
  return libcrux_sha3_simd_arm64__vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__veorq_n_u64(
    core_core_arch_arm_shared_neon_uint64x2_t a, uint64_t c) {
  core_core_arch_arm_shared_neon_uint64x2_t c0 =
      libcrux_intrinsics_arm64__vdupq_n_u64(c);
  return libcrux_intrinsics_arm64__veorq_u64(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_constant_fa(
    core_core_arch_arm_shared_neon_uint64x2_t a, uint64_t c) {
  return libcrux_sha3_simd_arm64__veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_fa(core_core_arch_arm_shared_neon_uint64x2_t a,
                               core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_intrinsics_arm64__veorq_u64(a, b);
}

static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_slice_2(
    Eurydice_slice a[2U], size_t start, size_t len, Eurydice_slice ret[2U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t,
                                     Eurydice_slice);
  ret[1U] = Eurydice_slice_subslice2(a[1U], start, start + len, uint8_t,
                                     Eurydice_slice);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_slice_n_fa(
    Eurydice_slice a[2U], size_t start, size_t len, Eurydice_slice ret[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, a, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[2U];
  libcrux_sha3_simd_arm64_slice_2(uu____0, start, len, ret0);
  memcpy(ret, ret0, (size_t)2U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE Eurydice_slice_uint8_t_2size_t__x2
libcrux_sha3_simd_arm64_split_at_mut_2(Eurydice_slice out[2U], size_t mid) {
  Eurydice_slice out0 = out[0U];
  Eurydice_slice out1 = out[1U];
  Eurydice_slice_uint8_t_x2 uu____0 = core_slice___Slice_T___split_at_mut(
      out0, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out00 = uu____0.fst;
  Eurydice_slice out01 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = core_slice___Slice_T___split_at_mut(
      out1, mid, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice out10 = uu____1.fst;
  Eurydice_slice out11 = uu____1.snd;
  Eurydice_slice_uint8_t_2size_t__x2 lit;
  lit.fst[0U] = out00;
  lit.fst[1U] = out10;
  lit.snd[0U] = out01;
  lit.snd[1U] = out11;
  return lit;
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
static KRML_MUSTINLINE Eurydice_slice_uint8_t_2size_t__x2
libcrux_sha3_simd_arm64_split_at_mut_n_fa(Eurydice_slice a[2U], size_t mid) {
  return libcrux_sha3_simd_arm64_split_at_mut_2(a, mid);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- $2size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_fc_s {
  core_core_arch_arm_shared_neon_uint64x2_t st[5U][5U];
} libcrux_sha3_generic_keccak_KeccakState_fc;

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0]#1}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_1e
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_fc
libcrux_sha3_generic_keccak_new_1e_12(void) {
  libcrux_sha3_generic_keccak_KeccakState_fc lit;
  lit.st[0U][0U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[0U][1U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[0U][2U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[0U][3U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[0U][4U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[1U][0U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[1U][1U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[1U][2U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[1U][3U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[1U][4U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[2U][0U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[2U][1U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[2U][2U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[2U][3U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[2U][4U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[3U][0U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[3U][1U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[3U][2U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[3U][3U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[3U][4U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[4U][0U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[4U][1U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[4U][2U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[4U][3U] = libcrux_sha3_simd_arm64_zero_fa();
  lit.st[4U][4U] = libcrux_sha3_simd_arm64_zero_fa();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_3c(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)72U - (size_t)8U,
                                 (size_t)72U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_fa_0f(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_3c(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_580(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)36, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)28, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c1(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_580(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_581(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)3, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)61, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c10(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_581(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f0(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c10(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_582(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)41, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)23, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c11(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_582(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f1(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c11(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_583(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)18, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)46, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c12(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_583(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f2(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c12(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c13(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_58(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f3(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c13(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_584(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)44, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)20, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c14(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_584(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f4(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c14(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_585(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)10, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)54, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c15(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_585(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f5(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c15(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_586(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)45, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)19, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c16(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_586(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f6(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c16(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_587(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)2, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)62, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c17(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_587(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f7(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c17(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_588(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)62, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)2, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c18(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_588(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f8(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c18(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_589(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)6, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)58, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c19(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_589(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f9(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c19(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5810(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)43, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)21, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c110(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5810(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f10(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c110(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5811(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)15, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)49, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c111(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5811(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f11(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c111(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5812(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)61, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)3, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c112(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5812(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f12(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c112(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5813(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)28, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)36, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c113(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5813(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f13(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c113(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5814(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)55, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)9, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c114(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5814(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f14(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c114(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5815(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)25, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)39, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c115(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5815(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f15(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c115(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5816(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)21, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)43, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c116(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5816(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f16(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c116(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5817(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)56, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)8, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c117(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5817(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f17(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c117(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5818(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)27, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)37, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c118(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5818(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f18(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c118(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5819(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)20, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)44, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c119(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5819(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f19(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c119(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5820(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)39, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)25, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c120(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5820(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f20(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c120(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5821(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)8, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)56, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c121(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5821(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f21(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c121(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_rotate_left_5822(
    core_core_arch_arm_shared_neon_uint64x2_t x) {
  return libcrux_intrinsics_arm64__veorq_u64(
      libcrux_intrinsics_arm64__vshlq_n_u64(
          (int32_t)14, x, core_core_arch_arm_shared_neon_uint64x2_t),
      libcrux_intrinsics_arm64__vshrq_n_u64(
          (int32_t)50, x, core_core_arch_arm_shared_neon_uint64x2_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64__vxarq_u64_c122(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  core_core_arch_arm_shared_neon_uint64x2_t ab =
      libcrux_intrinsics_arm64__veorq_u64(a, b);
  return libcrux_sha3_simd_arm64_rotate_left_5822(ab);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_fa
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE core_core_arch_arm_shared_neon_uint64x2_t
libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f22(
    core_core_arch_arm_shared_neon_uint64x2_t a,
    core_core_arch_arm_shared_neon_uint64x2_t b) {
  return libcrux_sha3_simd_arm64__vxarq_u64_c122(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_eb(
    libcrux_sha3_generic_keccak_KeccakState_fc *s) {
  core_core_arch_arm_shared_neon_uint64x2_t c[5U] = {
      libcrux_sha3_simd_arm64_xor5_fa(s->st[0U][0U], s->st[1U][0U],
                                      s->st[2U][0U], s->st[3U][0U],
                                      s->st[4U][0U]),
      libcrux_sha3_simd_arm64_xor5_fa(s->st[0U][1U], s->st[1U][1U],
                                      s->st[2U][1U], s->st[3U][1U],
                                      s->st[4U][1U]),
      libcrux_sha3_simd_arm64_xor5_fa(s->st[0U][2U], s->st[1U][2U],
                                      s->st[2U][2U], s->st[3U][2U],
                                      s->st[4U][2U]),
      libcrux_sha3_simd_arm64_xor5_fa(s->st[0U][3U], s->st[1U][3U],
                                      s->st[2U][3U], s->st[3U][3U],
                                      s->st[4U][3U]),
      libcrux_sha3_simd_arm64_xor5_fa(s->st[0U][4U], s->st[1U][4U],
                                      s->st[2U][4U], s->st[3U][4U],
                                      s->st[4U][4U])};
  core_core_arch_arm_shared_neon_uint64x2_t uu____0 =
      libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
          c[((size_t)0U + (size_t)4U) % (size_t)5U],
          c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____1 =
      libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
          c[((size_t)1U + (size_t)4U) % (size_t)5U],
          c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____2 =
      libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
          c[((size_t)2U + (size_t)4U) % (size_t)5U],
          c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____3 =
      libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
          c[((size_t)3U + (size_t)4U) % (size_t)5U],
          c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  core_core_arch_arm_shared_neon_uint64x2_t t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      libcrux_sha3_simd_arm64_rotate_left1_and_xor_fa(
          c[((size_t)4U + (size_t)4U) % (size_t)5U],
          c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = libcrux_sha3_simd_arm64_xor_fa(s->st[0U][0U], t[0U]);
  core_core_arch_arm_shared_neon_uint64x2_t uu____4 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f(s->st[1U][0U], t[0U]);
  s->st[1U][0U] = uu____4;
  core_core_arch_arm_shared_neon_uint64x2_t uu____5 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f0(s->st[2U][0U], t[0U]);
  s->st[2U][0U] = uu____5;
  core_core_arch_arm_shared_neon_uint64x2_t uu____6 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f1(s->st[3U][0U], t[0U]);
  s->st[3U][0U] = uu____6;
  core_core_arch_arm_shared_neon_uint64x2_t uu____7 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f2(s->st[4U][0U], t[0U]);
  s->st[4U][0U] = uu____7;
  core_core_arch_arm_shared_neon_uint64x2_t uu____8 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f3(s->st[0U][1U], t[1U]);
  s->st[0U][1U] = uu____8;
  core_core_arch_arm_shared_neon_uint64x2_t uu____9 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f4(s->st[1U][1U], t[1U]);
  s->st[1U][1U] = uu____9;
  core_core_arch_arm_shared_neon_uint64x2_t uu____10 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f5(s->st[2U][1U], t[1U]);
  s->st[2U][1U] = uu____10;
  core_core_arch_arm_shared_neon_uint64x2_t uu____11 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f6(s->st[3U][1U], t[1U]);
  s->st[3U][1U] = uu____11;
  core_core_arch_arm_shared_neon_uint64x2_t uu____12 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f7(s->st[4U][1U], t[1U]);
  s->st[4U][1U] = uu____12;
  core_core_arch_arm_shared_neon_uint64x2_t uu____13 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f8(s->st[0U][2U], t[2U]);
  s->st[0U][2U] = uu____13;
  core_core_arch_arm_shared_neon_uint64x2_t uu____14 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f9(s->st[1U][2U], t[2U]);
  s->st[1U][2U] = uu____14;
  core_core_arch_arm_shared_neon_uint64x2_t uu____15 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f10(s->st[2U][2U], t[2U]);
  s->st[2U][2U] = uu____15;
  core_core_arch_arm_shared_neon_uint64x2_t uu____16 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f11(s->st[3U][2U], t[2U]);
  s->st[3U][2U] = uu____16;
  core_core_arch_arm_shared_neon_uint64x2_t uu____17 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f12(s->st[4U][2U], t[2U]);
  s->st[4U][2U] = uu____17;
  core_core_arch_arm_shared_neon_uint64x2_t uu____18 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f13(s->st[0U][3U], t[3U]);
  s->st[0U][3U] = uu____18;
  core_core_arch_arm_shared_neon_uint64x2_t uu____19 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f14(s->st[1U][3U], t[3U]);
  s->st[1U][3U] = uu____19;
  core_core_arch_arm_shared_neon_uint64x2_t uu____20 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f15(s->st[2U][3U], t[3U]);
  s->st[2U][3U] = uu____20;
  core_core_arch_arm_shared_neon_uint64x2_t uu____21 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f16(s->st[3U][3U], t[3U]);
  s->st[3U][3U] = uu____21;
  core_core_arch_arm_shared_neon_uint64x2_t uu____22 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f17(s->st[4U][3U], t[3U]);
  s->st[4U][3U] = uu____22;
  core_core_arch_arm_shared_neon_uint64x2_t uu____23 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f18(s->st[0U][4U], t[4U]);
  s->st[0U][4U] = uu____23;
  core_core_arch_arm_shared_neon_uint64x2_t uu____24 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f19(s->st[1U][4U], t[4U]);
  s->st[1U][4U] = uu____24;
  core_core_arch_arm_shared_neon_uint64x2_t uu____25 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f20(s->st[2U][4U], t[4U]);
  s->st[2U][4U] = uu____25;
  core_core_arch_arm_shared_neon_uint64x2_t uu____26 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f21(s->st[3U][4U], t[4U]);
  s->st[3U][4U] = uu____26;
  core_core_arch_arm_shared_neon_uint64x2_t uu____27 =
      libcrux_sha3_simd_arm64_xor_and_rotate_fa_1f22(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_a0(
    libcrux_sha3_generic_keccak_KeccakState_fc *s) {
  core_core_arch_arm_shared_neon_uint64x2_t old[5U][5U];
  memcpy(old, s->st,
         (size_t)5U * sizeof(core_core_arch_arm_shared_neon_uint64x2_t[5U]));
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_b0(
    libcrux_sha3_generic_keccak_KeccakState_fc *s) {
  core_core_arch_arm_shared_neon_uint64x2_t old[5U][5U];
  memcpy(old, s->st,
         (size_t)5U * sizeof(core_core_arch_arm_shared_neon_uint64x2_t[5U]));
  for (size_t i0 = (size_t)0U; i0 < (size_t)5U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t j = i;
      s->st[i1][j] = libcrux_sha3_simd_arm64_and_not_xor_fa(
          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
          old[i1][(j + (size_t)1U) % (size_t)5U]);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_33(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, size_t i) {
  s->st[0U][0U] = libcrux_sha3_simd_arm64_xor_constant_fa(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_3e(
    libcrux_sha3_generic_keccak_KeccakState_fc *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_eb(s);
    libcrux_sha3_generic_keccak_pi_a0(s);
    libcrux_sha3_generic_keccak_chi_b0(s);
    libcrux_sha3_generic_keccak_iota_33(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_45(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_fa_0f(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_3e(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_load_block_3c(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_fa_07(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_3e(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_07(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_2f(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)72U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)72U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)72U - (size_t)8U, (size_t)72U,
                                 uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)72U - (size_t)8U, (size_t)72U,
                                 uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_9a(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_store_block_2f(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_fa_a5(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  libcrux_sha3_simd_arm64_store_block_full_9a(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_e7(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a5(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa
with const generics
- BLOCKSIZE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_fa_90(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  libcrux_sha3_simd_arm64_store_block_2f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_3f(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_simd_arm64_store_block_fa_90(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5d(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
  libcrux_sha3_simd_arm64_store_block_fa_90(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_70(
    libcrux_sha3_generic_keccak_KeccakState_fc s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(&s);
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a5(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_59(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_fc s =
      libcrux_sha3_generic_keccak_new_1e_12();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)72U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_fc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    libcrux_sha3_simd_arm64_slice_n_fa(uu____1, i0 * (size_t)72U, (size_t)72U,
                                       ret);
    libcrux_sha3_generic_keccak_absorb_block_45(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState_fc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  libcrux_sha3_simd_arm64_slice_n_fa(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_fe(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_e7(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)72U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_3f(&s, o0);
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
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            libcrux_sha3_simd_arm64_split_at_mut_n_fa(o1, (size_t)72U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5d(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_70(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_keccakx2_6e(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_59(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha512(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  uint8_t dummy[64U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)64U, dummy, uint8_t, Eurydice_slice)};
  libcrux_sha3_neon_keccakx2_6e(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_3c0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_fa_0f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_3c0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_450(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_fa_0f0(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_3e0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_load_block_3c0(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_fa_070(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_3e0(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe0(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_070(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_2f0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)136U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)136U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)136U - (size_t)8U,
                                 (size_t)136U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_9a0(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_store_block_2f0(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_fa_a50(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  libcrux_sha3_simd_arm64_store_block_full_9a0(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_e70(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a50(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa
with const generics
- BLOCKSIZE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_fa_900(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  libcrux_sha3_simd_arm64_store_block_2f0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_3f0(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_simd_arm64_store_block_fa_900(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5d0(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
  libcrux_sha3_simd_arm64_store_block_fa_900(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_700(
    libcrux_sha3_generic_keccak_KeccakState_fc s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(&s);
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a50(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_590(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_fc s =
      libcrux_sha3_generic_keccak_new_1e_12();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_fc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    libcrux_sha3_simd_arm64_slice_n_fa(uu____1, i0 * (size_t)136U, (size_t)136U,
                                       ret);
    libcrux_sha3_generic_keccak_absorb_block_450(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_fc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  libcrux_sha3_simd_arm64_slice_n_fa(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_fe0(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_e70(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_3f0(&s, o0);
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
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            libcrux_sha3_simd_arm64_split_at_mut_n_fa(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5d0(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_700(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_keccakx2_6e0(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_590(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha256(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  uint8_t dummy[32U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)32U, dummy, uint8_t, Eurydice_slice)};
  libcrux_sha3_neon_keccakx2_6e0(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe1(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_070(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_591(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_fc s =
      libcrux_sha3_generic_keccak_new_1e_12();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)136U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_fc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    libcrux_sha3_simd_arm64_slice_n_fa(uu____1, i0 * (size_t)136U, (size_t)136U,
                                       ret);
    libcrux_sha3_generic_keccak_absorb_block_450(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_fc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  libcrux_sha3_simd_arm64_slice_n_fa(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_fe1(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_e70(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)136U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_3f0(&s, o0);
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
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            libcrux_sha3_simd_arm64_split_at_mut_n_fa(o1, (size_t)136U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5d0(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_700(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_keccakx2_6e1(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_591(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_x2_shake256(Eurydice_slice input0,
                                                          Eurydice_slice input1,
                                                          Eurydice_slice out0,
                                                          Eurydice_slice out1) {
  Eurydice_slice buf0[2U] = {input0, input1};
  Eurydice_slice buf[2U] = {out0, out1};
  libcrux_sha3_neon_keccakx2_6e1(buf0, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_fc
    libcrux_sha3_neon_x2_incremental_KeccakState;

static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_fc
libcrux_sha3_neon_x2_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_12();
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_3c1(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_3e1(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_load_block_3c1(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_fa_071(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_3e1(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe2(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_071(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice data0,
    Eurydice_slice data1) {
  Eurydice_slice buf[2U] = {data0, data1};
  libcrux_sha3_generic_keccak_absorb_final_fe2(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_2f1(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)168U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)168U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)168U - (size_t)8U,
                                 (size_t)168U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa
with const generics
- BLOCKSIZE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_fa_901(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  libcrux_sha3_simd_arm64_store_block_2f1(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_3f1(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_simd_arm64_store_block_fa_901(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5d1(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
  libcrux_sha3_simd_arm64_store_block_fa_901(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_2e(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  Eurydice_slice_uint8_t_2size_t__x2 uu____0 =
      libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)168U);
  Eurydice_slice o0[2U];
  memcpy(o0, uu____0.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o10[2U];
  memcpy(o10, uu____0.snd, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_3f1(s, o0);
  Eurydice_slice_uint8_t_2size_t__x2 uu____1 =
      libcrux_sha3_simd_arm64_split_at_mut_n_fa(o10, (size_t)168U);
  Eurydice_slice o1[2U];
  memcpy(o1, uu____1.fst, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice o2[2U];
  memcpy(o2, uu____1.snd, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_5d1(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_5d1(s, o2);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_2e(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out0,
    Eurydice_slice out1) {
  Eurydice_slice buf[2U] = {out0, out1};
  libcrux_sha3_generic_keccak_squeeze_next_block_5d1(s, buf);
}

typedef libcrux_sha3_generic_keccak_KeccakState_48
    libcrux_sha3_portable_KeccakState;

static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake128_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_7a();
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_de1(
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
- BLOCKSIZE= 168
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
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_252(
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
  libcrux_sha3_portable_keccak_load_block_full_5a_2d1(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data0) {
  Eurydice_slice buf[1U] = {data0};
  libcrux_sha3_generic_keccak_absorb_final_252(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_391(
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_481(
    uint64_t (*a)[5U], Eurydice_slice b[1U]) {
  libcrux_sha3_portable_keccak_store_block_391(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
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
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c81(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(s);
  libcrux_sha3_portable_keccak_store_block_5a_481(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_three_blocks_4d(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_581(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o2[1U];
  memcpy(o2, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o1);
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o2);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_three_blocks_4d(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, buf);
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

static KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd2(buf0, buf);
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

static KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest,
                                                         Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd3(buf0, buf);
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
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5a_df3(
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_123(
    libcrux_sha3_generic_keccak_KeccakState_48 s, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccakf1600_13(&s);
  uint8_t b[1U][200U];
  libcrux_sha3_portable_keccak_store_block_full_5a_883(s.st, b);
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
  libcrux_sha3_generic_keccak_absorb_final_252(uu____2, ret);
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
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)168U);
        Eurydice_slice o[1U];
        memcpy(o, uu____5.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____5.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c81(&s, o);
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

static KRML_MUSTINLINE void libcrux_sha3_portable_shake128(
    Eurydice_slice digest, Eurydice_slice data) {
  Eurydice_slice buf0[1U] = {data};
  Eurydice_slice buf[1U] = {digest};
  libcrux_sha3_portable_keccakx1_fd4(buf0, buf);
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

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_3c2(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_fa_0f1(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_3c2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_451(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_fa_0f1(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_3e2(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_load_block_3c2(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_fa_072(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_3e2(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe3(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_072(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_2f2(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)144U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)144U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)144U - (size_t)8U,
                                 (size_t)144U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_9a1(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_store_block_2f2(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_fa_a51(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  libcrux_sha3_simd_arm64_store_block_full_9a1(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_e71(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a51(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa
with const generics
- BLOCKSIZE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_fa_902(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  libcrux_sha3_simd_arm64_store_block_2f2(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_3f2(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_simd_arm64_store_block_fa_902(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5d2(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
  libcrux_sha3_simd_arm64_store_block_fa_902(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_701(
    libcrux_sha3_generic_keccak_KeccakState_fc s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(&s);
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a51(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_592(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_fc s =
      libcrux_sha3_generic_keccak_new_1e_12();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)144U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_fc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    libcrux_sha3_simd_arm64_slice_n_fa(uu____1, i0 * (size_t)144U, (size_t)144U,
                                       ret);
    libcrux_sha3_generic_keccak_absorb_block_451(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState_fc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  libcrux_sha3_simd_arm64_slice_n_fa(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_fe3(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_e71(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)144U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_3f2(&s, o0);
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
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            libcrux_sha3_simd_arm64_split_at_mut_n_fa(o1, (size_t)144U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5d2(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_701(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_keccakx2_6e2(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_592(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  uint8_t dummy[28U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)28U, dummy, uint8_t, Eurydice_slice)};
  libcrux_sha3_neon_keccakx2_6e2(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_3c3(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice blocks[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[0U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vld1q_bytes_u64(Eurydice_slice_subslice2(
            blocks[1U], (size_t)16U * i0, (size_t)16U * (i0 + (size_t)1U),
            uint8_t, Eurydice_slice));
    s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U] =
        libcrux_intrinsics_arm64__veorq_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            libcrux_intrinsics_arm64__vtrn1q_u64(v0, v1));
    s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)2U * i0 + (size_t)1U) % (size_t)5U] =
         libcrux_intrinsics_arm64__veorq_u64(
             s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
              [((size_t)2U * i0 + (size_t)1U) % (size_t)5U],
             libcrux_intrinsics_arm64__vtrn2q_u64(v0, v1));
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint64_t u[2U] = {0U};
    uint8_t uu____0[8U];
    core_result_Result_56 dst0;
    Eurydice_slice_to_array2(
        &dst0,
        Eurydice_slice_subslice2(blocks[0U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst0, uu____0);
    u[0U] = core_num__u64_9__from_le_bytes(uu____0);
    uint8_t uu____1[8U];
    core_result_Result_56 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks[1U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice),
        Eurydice_slice, uint8_t[8U], void *);
    core_result_unwrap_41_ac(dst, uu____1);
    u[1U] = core_num__u64_9__from_le_bytes(uu____1);
    core_core_arch_arm_shared_neon_uint64x2_t uvec =
        libcrux_intrinsics_arm64__vld1q_u64(
            Eurydice_array_to_slice((size_t)2U, u, uint64_t, Eurydice_slice));
    s[i][j] = libcrux_intrinsics_arm64__veorq_u64(s[i][j], uvec);
  }
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_fa
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_fa_0f2(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, b, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_3c3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_452(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice blocks[2U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[2U];
  memcpy(uu____1, blocks, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_simd_arm64_load_block_fa_0f2(uu____0, uu____1);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_3e3(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    uint8_t blocks[2U][200U]) {
  Eurydice_slice buf[2U] = {Eurydice_array_to_slice((size_t)200U, blocks[0U],
                                                    uint8_t, Eurydice_slice),
                            Eurydice_array_to_slice((size_t)200U, blocks[1U],
                                                    uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_load_block_3c3(s, buf);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_full_fa
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_load_block_full_fa_073(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t b[2U][200U]) {
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____0)[5U] = a;
  uint8_t uu____1[2U][200U];
  memcpy(uu____1, b, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_3e3(uu____0, uu____1);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_fe4(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice last[2U]) {
  size_t last_len = core_slice___Slice_T___len(last[0U], uint8_t, size_t);
  uint8_t blocks[2U][200U] = {{0U}};
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
  core_core_arch_arm_shared_neon_uint64x2_t(*uu____3)[5U] = s->st;
  uint8_t uu____4[2U][200U];
  memcpy(uu____4, blocks, (size_t)2U * sizeof(uint8_t[200U]));
  libcrux_sha3_simd_arm64_load_block_full_fa_073(uu____3, uu____4);
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_2f3(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U],
    Eurydice_slice out[2U]) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++) {
    size_t i0 = i;
    core_core_arch_arm_shared_neon_uint64x2_t v0 =
        libcrux_intrinsics_arm64__vtrn1q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    core_core_arch_arm_shared_neon_uint64x2_t v1 =
        libcrux_intrinsics_arm64__vtrn2q_u64(
            s[(size_t)2U * i0 / (size_t)5U][(size_t)2U * i0 % (size_t)5U],
            s[((size_t)2U * i0 + (size_t)1U) / (size_t)5U]
             [((size_t)2U * i0 + (size_t)1U) % (size_t)5U]);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[0U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v0);
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_slice_subslice2(out[1U], (size_t)16U * i0,
                                 (size_t)16U * (i0 + (size_t)1U), uint8_t,
                                 Eurydice_slice),
        v1);
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U) {
    size_t i = ((size_t)104U / (size_t)8U - (size_t)1U) / (size_t)5U;
    size_t j = ((size_t)104U / (size_t)8U - (size_t)1U) % (size_t)5U;
    uint8_t u[16U] = {0U};
    libcrux_intrinsics_arm64__vst1q_bytes_u64(
        Eurydice_array_to_slice((size_t)16U, u, uint8_t, Eurydice_slice),
        s[i][j]);
    Eurydice_slice uu____0 =
        Eurydice_slice_subslice2(out[0U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____0,
        Eurydice_array_to_subslice2(u, (size_t)0U, (size_t)8U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
    Eurydice_slice uu____1 =
        Eurydice_slice_subslice2(out[1U], (size_t)104U - (size_t)8U,
                                 (size_t)104U, uint8_t, Eurydice_slice);
    core_slice___Slice_T___copy_from_slice(
        uu____1,
        Eurydice_array_to_subslice2(u, (size_t)8U, (size_t)16U, uint8_t,
                                    Eurydice_slice),
        uint8_t, void *);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_9a2(
    core_core_arch_arm_shared_neon_uint64x2_t (*s)[5U], uint8_t ret[2U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  Eurydice_slice buf[2U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t, Eurydice_slice),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t, Eurydice_slice)};
  libcrux_sha3_simd_arm64_store_block_2f3(s, buf);
  uint8_t uu____0[200U];
  memcpy(uu____0, out0, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____1[200U];
  memcpy(uu____1, out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], uu____0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], uu____1, (size_t)200U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_full_fa
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_full_fa_a52(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], uint8_t ret[2U][200U]) {
  libcrux_sha3_simd_arm64_store_block_full_9a2(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_and_last_e72(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a52(s->st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<2:
usize> for core::core_arch::arm_shared::neon::uint64x2_t)}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block_fa
with const generics
- BLOCKSIZE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_simd_arm64_store_block_fa_903(
    core_core_arch_arm_shared_neon_uint64x2_t (*a)[5U], Eurydice_slice b[2U]) {
  libcrux_sha3_simd_arm64_store_block_2f3(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_3f3(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_simd_arm64_store_block_fa_903(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_5d3(
    libcrux_sha3_generic_keccak_KeccakState_fc *s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(s);
  libcrux_sha3_simd_arm64_store_block_fa_903(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_last_702(
    libcrux_sha3_generic_keccak_KeccakState_fc s, Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_keccakf1600_3e(&s);
  uint8_t b[2U][200U];
  libcrux_sha3_simd_arm64_store_block_full_fa_a52(s.st, b);
  for (size_t i = (size_t)0U; i < (size_t)2U; i++) {
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
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_593(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  libcrux_sha3_generic_keccak_KeccakState_fc s =
      libcrux_sha3_generic_keccak_new_1e_12();
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(data[0U], uint8_t, size_t) / (size_t)104U;
       i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_fc *uu____0 = &s;
    Eurydice_slice uu____1[2U];
    memcpy(uu____1, data, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice ret[2U];
    libcrux_sha3_simd_arm64_slice_n_fa(uu____1, i0 * (size_t)104U, (size_t)104U,
                                       ret);
    libcrux_sha3_generic_keccak_absorb_block_452(uu____0, ret);
  }
  size_t rem =
      core_slice___Slice_T___len(data[0U], uint8_t, size_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState_fc *uu____2 = &s;
  Eurydice_slice uu____3[2U];
  memcpy(uu____3, data, (size_t)2U * sizeof(Eurydice_slice));
  Eurydice_slice ret[2U];
  libcrux_sha3_simd_arm64_slice_n_fa(
      uu____3, core_slice___Slice_T___len(data[0U], uint8_t, size_t) - rem, rem,
      ret);
  libcrux_sha3_generic_keccak_absorb_final_fe4(uu____2, ret);
  size_t outlen = core_slice___Slice_T___len(out[0U], uint8_t, size_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_e72(&s, out);
  } else {
    Eurydice_slice_uint8_t_2size_t__x2 uu____4 =
        libcrux_sha3_simd_arm64_split_at_mut_n_fa(out, (size_t)104U);
    Eurydice_slice o0[2U];
    memcpy(o0, uu____4.fst, (size_t)2U * sizeof(Eurydice_slice));
    Eurydice_slice o1[2U];
    memcpy(o1, uu____4.snd, (size_t)2U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_3f3(&s, o0);
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
        Eurydice_slice_uint8_t_2size_t__x2 uu____5 =
            libcrux_sha3_simd_arm64_split_at_mut_n_fa(o1, (size_t)104U);
        Eurydice_slice o[2U];
        memcpy(o, uu____5.fst, (size_t)2U * sizeof(Eurydice_slice));
        Eurydice_slice orest[2U];
        memcpy(orest, uu____5.snd, (size_t)2U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_5d3(&s, o);
        memcpy(o1, orest, (size_t)2U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      libcrux_sha3_generic_keccak_squeeze_last_702(s, o1);
    }
  }
}

/**
A monomorphic instance of libcrux_sha3.neon.keccakx2
with const generics
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_neon_keccakx2_6e3(
    Eurydice_slice data[2U], Eurydice_slice out[2U]) {
  Eurydice_slice uu____0[2U];
  memcpy(uu____0, data, (size_t)2U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_keccak_593(uu____0, out);
}

static KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest,
                                                     Eurydice_slice data) {
  uint8_t dummy[48U] = {0U};
  Eurydice_slice uu____0[2U] = {data, data};
  Eurydice_slice buf[2U] = {
      digest,
      Eurydice_array_to_slice((size_t)48U, dummy, uint8_t, Eurydice_slice)};
  libcrux_sha3_neon_keccakx2_6e3(uu____0, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_squeeze_first_five_blocks_34(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out[1U]) {
  Eurydice_slice_uint8_t_1size_t__x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
  Eurydice_slice o0[1U];
  memcpy(o0, uu____0.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o10[1U];
  memcpy(o10, uu____0.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_first_block_581(s, o0);
  Eurydice_slice_uint8_t_1size_t__x2 uu____1 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o10, (size_t)168U);
  Eurydice_slice o1[1U];
  memcpy(o1, uu____1.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o20[1U];
  memcpy(o20, uu____1.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o1);
  Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o20, (size_t)168U);
  Eurydice_slice o2[1U];
  memcpy(o2, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o30[1U];
  memcpy(o30, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o2);
  Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
      libcrux_sha3_portable_keccak_split_at_mut_n_5a(o30, (size_t)168U);
  Eurydice_slice o3[1U];
  memcpy(o3, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
  Eurydice_slice o4[1U];
  memcpy(o4, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o3);
  libcrux_sha3_generic_keccak_squeeze_next_block_c81(s, o4);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out0) {
  Eurydice_slice buf[1U] = {out0};
  libcrux_sha3_generic_keccak_squeeze_first_five_blocks_34(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice data) {
  Eurydice_slice buf[1U] = {data};
  libcrux_sha3_generic_keccak_absorb_final_251(s, buf);
}

static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_incremental_shake256_init(void) {
  return libcrux_sha3_generic_keccak_new_1e_7a();
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_first_block_580(s, buf);
}

static KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_48 *s, Eurydice_slice out) {
  Eurydice_slice buf[1U] = {out};
  libcrux_sha3_generic_keccak_squeeze_next_block_c80(s, buf);
}

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::portable::KeccakState)}
*/
static inline libcrux_sha3_generic_keccak_KeccakState_48
libcrux_sha3_portable_clone_3d(
    libcrux_sha3_generic_keccak_KeccakState_48 *self) {
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

typedef core_core_arch_arm_shared_neon_uint64x2_t
    libcrux_sha3_simd_arm64_uint64x2_t;

typedef libcrux_sha3_generic_keccak_KeccakState_fc
    libcrux_sha3_neon_x2_incremental_KeccakState2Internal;

typedef uint8_t libcrux_sha3_Sha3_512Digest[64U];

typedef uint8_t libcrux_sha3_Sha3_384Digest[48U];

typedef uint8_t libcrux_sha3_Sha3_256Digest[32U];

typedef uint8_t libcrux_sha3_Sha3_224Digest[28U];

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_portable_H_DEFINED
#endif
