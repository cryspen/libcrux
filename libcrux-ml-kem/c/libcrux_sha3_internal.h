/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: d250df809d9b0fa1bddac2055794620e87f435cc
 * Eurydice: 574bc5d60d562a5b513bd8d09e36fac0b6a111d3
 * Karamel: 5e16cd5abf3f2323b0d27e3070ec2974657a391b
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 40755e06b5ac176a1a8cfe5fa12adead07c1aef7
 */

#ifndef __libcrux_sha3_internal_H
#define __libcrux_sha3_internal_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

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

static KRML_MUSTINLINE Eurydice_slice_uint8_t_x2
libcrux_sha3_portable_keccak_split_at_mut_1(Eurydice_slice out, size_t mid) {
  return Eurydice_slice_split_at_mut(out, mid, uint8_t,
                                     Eurydice_slice_uint8_t_x2);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<1:
usize> for u64)}
*/
static KRML_MUSTINLINE Eurydice_slice_uint8_t_1size_t__x2
libcrux_sha3_portable_keccak_split_at_mut_n_5a(Eurydice_slice a[1U],
                                               size_t mid) {
  Eurydice_slice_uint8_t_x2 uu____0 =
      libcrux_sha3_portable_keccak_split_at_mut_1(a[0U], mid);
  Eurydice_slice x = uu____0.fst;
  Eurydice_slice y = uu____0.snd;
  Eurydice_slice_uint8_t_1size_t__x2 lit;
  lit.fst[0U] = x;
  lit.snd[0U] = y;
  return lit;
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
  uint64_t repeat_expression0[5U][5U];
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, uint64_t repeat_expression[5U];
      KRML_MAYBE_FOR5(
          i, (size_t)0U, (size_t)5U, (size_t)1U,
          repeat_expression[i] = libcrux_sha3_portable_keccak_zero_5a(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)5U * sizeof(uint64_t)););
  memcpy(lit.st, repeat_expression0, (size_t)5U * sizeof(uint64_t[5U]));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_3a(
    uint64_t (*state)[5U], Eurydice_slice blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    core_result_Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks, offset, offset + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U], core_array_TryFromSliceError);
    core_result_unwrap_26_68(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    state[uu____1][uu____2] =
        state[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_3a(
    uint64_t (*state)[5U], uint8_t *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_3a(
      state, Eurydice_array_to_slice((size_t)200U, blocks, uint8_t), start);
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
    uint64_t (*state)[5U], uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_portable_keccak_load_block_full_3a(state, blocks[0U], start);
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
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 31U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)168U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_3a(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_3a(
    uint64_t (*s)[5U], Eurydice_slice out) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
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
    uint64_t (*state)[5U], Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_3a(state, out[0U]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_5a_3a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_3a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_5b(
    uint64_t (*state)[5U], Eurydice_slice blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    core_result_Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks, offset, offset + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U], core_array_TryFromSliceError);
    core_result_unwrap_26_68(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    state[uu____1][uu____2] =
        state[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
  }
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_5b(
    uint64_t (*state)[5U], uint8_t *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_5b(
      state, Eurydice_array_to_slice((size_t)200U, blocks, uint8_t), start);
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
    uint64_t (*state)[5U], uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_portable_keccak_load_block_full_5b(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e0(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 31U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5b(
    uint64_t (*s)[5U], Eurydice_slice out) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
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
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_5a_5b(
    uint64_t (*state)[5U], Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_5b(state, out[0U]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
  libcrux_sha3_portable_keccak_store_block_5a_5b(s->st, out);
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
    uint64_t (*state)[5U], Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_5b(state, blocks[0U], start);
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
    uint64_t (*state)[5U], Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_3a(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_portable_keccak_load_block_5a_3a(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_3a(
    uint64_t (*s)[5U], uint8_t *out) {
  libcrux_sha3_portable_keccak_store_block_3a(
      s, Eurydice_array_to_slice((size_t)200U, out, uint8_t));
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
    uint64_t (*state)[5U], uint8_t (*out)[200U]) {
  libcrux_sha3_portable_keccak_store_block_full_3a(state, out[0U]);
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_3a(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_3a(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)168U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c63(&s, data, i0 * (size_t)168U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)168U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c63(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)168U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c6(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)168U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c6(&s, o);
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e4(data, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_7a(
    uint64_t (*state)[5U], Eurydice_slice blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    core_result_Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks, offset, offset + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U], core_array_TryFromSliceError);
    core_result_unwrap_26_68(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    state[uu____1][uu____2] =
        state[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
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
    uint64_t (*state)[5U], Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_7a(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_portable_keccak_load_block_5a_7a(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_7a(
    uint64_t (*state)[5U], uint8_t *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_7a(
      state, Eurydice_array_to_slice((size_t)200U, blocks, uint8_t), start);
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
    uint64_t (*state)[5U], uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_portable_keccak_load_block_full_7a(state, blocks[0U], start);
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
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)104U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_7a(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_7a(
    uint64_t (*s)[5U], Eurydice_slice out) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
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
    uint64_t (*s)[5U], uint8_t *out) {
  libcrux_sha3_portable_keccak_store_block_7a(
      s, Eurydice_array_to_slice((size_t)200U, out, uint8_t));
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
    uint64_t (*state)[5U], uint8_t (*out)[200U]) {
  libcrux_sha3_portable_keccak_store_block_full_7a(state, out[0U]);
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_7a(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    uint64_t (*state)[5U], Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_7a(state, out[0U]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_7a(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)104U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c62(&s, data, i0 * (size_t)104U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)104U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e4(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c62(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)104U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c63(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)104U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e3(data, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_2c(
    uint64_t (*state)[5U], Eurydice_slice blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    core_result_Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks, offset, offset + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U], core_array_TryFromSliceError);
    core_result_unwrap_26_68(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    state[uu____1][uu____2] =
        state[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
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
    uint64_t (*state)[5U], Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_2c(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_portable_keccak_load_block_5a_2c(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_2c(
    uint64_t (*state)[5U], uint8_t *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_2c(
      state, Eurydice_array_to_slice((size_t)200U, blocks, uint8_t), start);
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
    uint64_t (*state)[5U], uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_portable_keccak_load_block_full_2c(state, blocks[0U], start);
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
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)144U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_2c(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_2c(
    uint64_t (*s)[5U], Eurydice_slice out) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
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
    uint64_t (*s)[5U], uint8_t *out) {
  libcrux_sha3_portable_keccak_store_block_2c(
      s, Eurydice_array_to_slice((size_t)200U, out, uint8_t));
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
    uint64_t (*state)[5U], uint8_t (*out)[200U]) {
  libcrux_sha3_portable_keccak_store_block_full_2c(state, out[0U]);
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_2c(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    uint64_t (*state)[5U], Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_2c(state, out[0U]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_2c(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)144U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c61(&s, data, i0 * (size_t)144U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)144U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e3(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c61(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)144U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c62(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)144U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e2(data, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_portable_keccak_load_block_5a_5b(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_full_5b(
    uint64_t (*s)[5U], uint8_t *out) {
  libcrux_sha3_portable_keccak_store_block_5b(
      s, Eurydice_array_to_slice((size_t)200U, out, uint8_t));
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
    uint64_t (*state)[5U], uint8_t (*out)[200U]) {
  libcrux_sha3_portable_keccak_store_block_full_5b(state, out[0U]);
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_5b(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
        uint8_t);
  }
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_5b(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
        uint8_t);
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
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccak_9e1(
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c60(&s, data, i0 * (size_t)136U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e0(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c60(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c60(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e1(data, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e2(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)136U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_5b(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c60(&s, data, i0 * (size_t)136U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e2(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c60(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)136U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c60(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)136U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e0(data, out);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_f8(
    uint64_t (*state)[5U], Eurydice_slice blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    uint8_t uu____0[8U];
    core_result_Result_15 dst;
    Eurydice_slice_to_array2(
        &dst,
        Eurydice_slice_subslice2(blocks, offset, offset + (size_t)8U, uint8_t),
        Eurydice_slice, uint8_t[8U], core_array_TryFromSliceError);
    core_result_unwrap_26_68(dst, uu____0);
    size_t uu____1 = i0 / (size_t)5U;
    size_t uu____2 = i0 % (size_t)5U;
    state[uu____1][uu____2] =
        state[uu____1][uu____2] ^ core_num__u64_9__from_le_bytes(uu____0);
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
    uint64_t (*state)[5U], Eurydice_slice *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_f8(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_block_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *blocks,
    size_t start) {
  libcrux_sha3_portable_keccak_load_block_5a_f8(s->st, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.load_block_full
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_load_block_full_f8(
    uint64_t (*state)[5U], uint8_t *blocks, size_t start) {
  libcrux_sha3_portable_keccak_load_block_f8(
      state, Eurydice_array_to_slice((size_t)200U, blocks, uint8_t), start);
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
    uint64_t (*state)[5U], uint8_t (*blocks)[200U], size_t start) {
  libcrux_sha3_portable_keccak_load_block_full_f8(state, blocks[0U], start);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_absorb_final_9e1(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *last,
    size_t start, size_t len) {
  uint8_t blocks[1U][200U] = {{0U}};
  {
    size_t i = (size_t)0U;
    if (len > (size_t)0U) {
      Eurydice_slice uu____0 =
          Eurydice_array_to_subslice2(blocks[i], (size_t)0U, len, uint8_t);
      Eurydice_slice_copy(
          uu____0,
          Eurydice_slice_subslice2(last[i], start, start + len, uint8_t),
          uint8_t);
    }
    blocks[i][len] = 6U;
    size_t uu____1 = i;
    size_t uu____2 = (size_t)72U - (size_t)1U;
    blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;
  }
  libcrux_sha3_portable_keccak_load_block_full_5a_f8(s->st, blocks, (size_t)0U);
  libcrux_sha3_generic_keccak_keccakf1600_04(s);
}

/**
A monomorphic instance of libcrux_sha3.portable_keccak.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_portable_keccak_store_block_f8(
    uint64_t (*s)[5U], Eurydice_slice out) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice uu____0 = Eurydice_slice_subslice2(
        out, (size_t)8U * i0, (size_t)8U * i0 + (size_t)8U, uint8_t);
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
    uint64_t (*s)[5U], uint8_t *out) {
  libcrux_sha3_portable_keccak_store_block_f8(
      s, Eurydice_array_to_slice((size_t)200U, out, uint8_t));
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
    uint64_t (*state)[5U], uint8_t (*out)[200U]) {
  libcrux_sha3_portable_keccak_store_block_full_f8(state, out[0U]);
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_f8(s->st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    uint64_t (*state)[5U], Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_f8(state, out[0U]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_first_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
  libcrux_sha3_portable_keccak_store_block_5a_f8(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
static KRML_MUSTINLINE void libcrux_sha3_generic_keccak_squeeze_next_block_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice *out) {
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
  uint8_t b[1U][200U] = {{0U}};
  libcrux_sha3_portable_keccak_store_block_full_5a_f8(s.st, b);
  {
    size_t i = (size_t)0U;
    Eurydice_slice uu____0 = out[i];
    uint8_t *uu____1 = b[i];
    core_ops_range_Range_08 lit;
    lit.start = (size_t)0U;
    lit.end = Eurydice_slice_len(out[i], uint8_t);
    Eurydice_slice_copy(
        uu____0,
        Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                   core_ops_range_Range_08, __builtin_slice_t),
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_KeccakState_17 s =
      libcrux_sha3_generic_keccak_new_89_04();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)72U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_absorb_block_c6(&s, data, i0 * (size_t)72U);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)72U;
  libcrux_sha3_generic_keccak_KeccakState_17 *uu____0 = &s;
  Eurydice_slice *uu____1 = data;
  libcrux_sha3_generic_keccak_absorb_final_9e1(
      uu____0, uu____1, Eurydice_slice_len(data[0U], uint8_t) - rem, rem);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U) {
    libcrux_sha3_generic_keccak_squeeze_first_and_last_c6(&s, out);
  } else {
    Eurydice_slice_uint8_t_1size_t__x2 uu____2 =
        libcrux_sha3_portable_keccak_split_at_mut_n_5a(out, (size_t)72U);
    Eurydice_slice o0[1U];
    memcpy(o0, uu____2.fst, (size_t)1U * sizeof(Eurydice_slice));
    Eurydice_slice o1[1U];
    memcpy(o1, uu____2.snd, (size_t)1U * sizeof(Eurydice_slice));
    libcrux_sha3_generic_keccak_squeeze_first_block_c61(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_Clause1_Item__I__for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, size_t, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_A__for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_1size_t__x2 uu____3 =
            libcrux_sha3_portable_keccak_split_at_mut_n_5a(o1, (size_t)72U);
        Eurydice_slice o[1U];
        memcpy(o, uu____3.fst, (size_t)1U * sizeof(Eurydice_slice));
        Eurydice_slice orest[1U];
        memcpy(orest, uu____3.snd, (size_t)1U * sizeof(Eurydice_slice));
        libcrux_sha3_generic_keccak_squeeze_next_block_c61(&s, o);
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
    Eurydice_slice *data, Eurydice_slice out[1U]) {
  libcrux_sha3_generic_keccak_keccak_9e(data, out);
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_internal_H_DEFINED
#endif
