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
 * Libcrux: 2e8f138dbcbfbfabf4bbd994c8587ec00d197102
 */

#include "internal/libcrux_sha3_avx2.h"

#include "internal/libcrux_core.h"

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i zero_ef(void) {
  return mm256_set1_epi64x((int64_t)0);
}

static KRML_MUSTINLINE __m256i _veor5q_u64(__m256i a, __m256i b, __m256i c,
                                           __m256i d, __m256i e) {
  __m256i ab = mm256_xor_si256(a, b);
  __m256i cd = mm256_xor_si256(c, d);
  __m256i abcd = mm256_xor_si256(ab, cd);
  return mm256_xor_si256(abcd, e);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i xor5_ef(__m256i a, __m256i b, __m256i c,
                                       __m256i d, __m256i e) {
  return _veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE __m256i rotate_left_76(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)1, x, __m256i),
                         mm256_srli_epi64((int32_t)63, x, __m256i));
}

static KRML_MUSTINLINE __m256i _vrax1q_u64(__m256i a, __m256i b) {
  __m256i uu____0 = a;
  return mm256_xor_si256(uu____0, rotate_left_76(b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i rotate_left1_and_xor_ef(__m256i a, __m256i b) {
  return _vrax1q_u64(a, b);
}

static KRML_MUSTINLINE __m256i _vbcaxq_u64(__m256i a, __m256i b, __m256i c) {
  return mm256_xor_si256(a, mm256_andnot_si256(c, b));
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i and_not_xor_ef(__m256i a, __m256i b, __m256i c) {
  return _vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE __m256i _veorq_n_u64(__m256i a, uint64_t c) {
  __m256i c0 = mm256_set1_epi64x(
      (int64_t) /* Casting here is required, doesn't change the value. */ c);
  return mm256_xor_si256(a, c0);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i xor_constant_ef(__m256i a, uint64_t c) {
  return _veorq_n_u64(a, c);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE __m256i xor_ef(__m256i a, __m256i b) {
  return mm256_xor_si256(a, b);
}

static KRML_MUSTINLINE void slice_4(Eurydice_slice a[4U], size_t start,
                                    size_t len, Eurydice_slice ret[4U]) {
  ret[0U] = Eurydice_slice_subslice2(a[0U], start, start + len, uint8_t);
  ret[1U] = Eurydice_slice_subslice2(a[1U], start, start + len, uint8_t);
  ret[2U] = Eurydice_slice_subslice2(a[2U], start, start + len, uint8_t);
  ret[3U] = Eurydice_slice_subslice2(a[3U], start, start + len, uint8_t);
}

/**
This function found in impl {(libcrux_sha3::traits::internal::KeccakItem<4:
usize> for core::core_arch::x86::__m256i)}
*/
static KRML_MUSTINLINE void slice_n_ef(Eurydice_slice a[4U], size_t start,
                                       size_t len, Eurydice_slice ret[4U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_a[4U];
  memcpy(copy_of_a, a, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret0[4U];
  slice_4(copy_of_a, start, len, ret0);
  memcpy(ret, ret0, (size_t)4U * sizeof(Eurydice_slice));
}

static KRML_MUSTINLINE Eurydice_slice_uint8_t_4size_t__x2
split_at_mut_4(Eurydice_slice out[4U], size_t mid) {
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
static KRML_MUSTINLINE Eurydice_slice_uint8_t_4size_t__x2
split_at_mut_n_ef(Eurydice_slice a[4U], size_t mid) {
  return split_at_mut_4(a, mid);
}

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
static KRML_MUSTINLINE libcrux_sha3_generic_keccak_KeccakState_55
new_89_a6(void) {
  libcrux_sha3_generic_keccak_KeccakState_55 lit;
  lit.st[0U][0U] = zero_ef();
  lit.st[0U][1U] = zero_ef();
  lit.st[0U][2U] = zero_ef();
  lit.st[0U][3U] = zero_ef();
  lit.st[0U][4U] = zero_ef();
  lit.st[1U][0U] = zero_ef();
  lit.st[1U][1U] = zero_ef();
  lit.st[1U][2U] = zero_ef();
  lit.st[1U][3U] = zero_ef();
  lit.st[1U][4U] = zero_ef();
  lit.st[2U][0U] = zero_ef();
  lit.st[2U][1U] = zero_ef();
  lit.st[2U][2U] = zero_ef();
  lit.st[2U][3U] = zero_ef();
  lit.st[2U][4U] = zero_ef();
  lit.st[3U][0U] = zero_ef();
  lit.st[3U][1U] = zero_ef();
  lit.st[3U][2U] = zero_ef();
  lit.st[3U][3U] = zero_ef();
  lit.st[3U][4U] = zero_ef();
  lit.st[4U][0U] = zero_ef();
  lit.st[4U][1U] = zero_ef();
  lit.st[4U][2U] = zero_ef();
  lit.st[4U][3U] = zero_ef();
  lit.st[4U][4U] = zero_ef();
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void load_block_5b(__m256i (*s)[5U],
                                          Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v00 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v10 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v20 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v30 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v0l = mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = mm256_permute2x128_si256((int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = mm256_permute2x128_si256((int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = mm256_permute2x128_si256((int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = mm256_permute2x128_si256((int32_t)49, v1h, v3h, __m256i);
    s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U] =
        mm256_xor_si256(
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U], v0);
    s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)1U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
                         v1);
    s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)2U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
                         v2);
    s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)3U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
                         v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
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
  __m256i u = mm256_loadu_si256_u8(core_array___Array_T__N__23__as_slice(
      (size_t)32U, u8s, uint8_t, Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = mm256_xor_si256(s[i0][j0], u);
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
    __m256i u0 = mm256_loadu_si256_u8(core_array___Array_T__N__23__as_slice(
        (size_t)32U, u8s0, uint8_t, Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    s[i][j] = mm256_xor_si256(s[i][j], u0);
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
static KRML_MUSTINLINE void load_block_ef_5b(__m256i (*a)[5U],
                                             Eurydice_slice b[4U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_b[4U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(Eurydice_slice));
  load_block_5b(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE __m256i rotate_left_02(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)36, x, __m256i),
                         mm256_srli_epi64((int32_t)28, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_02(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_02(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_02(__m256i a, __m256i b) {
  return _vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE __m256i rotate_left_ac(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)3, x, __m256i),
                         mm256_srli_epi64((int32_t)61, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_ac(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_ac(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_ac(__m256i a, __m256i b) {
  return _vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE __m256i rotate_left_020(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)41, x, __m256i),
                         mm256_srli_epi64((int32_t)23, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_020(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_020(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_020(__m256i a, __m256i b) {
  return _vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE __m256i rotate_left_a9(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)18, x, __m256i),
                         mm256_srli_epi64((int32_t)46, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_a9(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_a9(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_a9(__m256i a, __m256i b) {
  return _vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_76(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_76(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_76(__m256i a, __m256i b) {
  return _vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE __m256i rotate_left_58(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)44, x, __m256i),
                         mm256_srli_epi64((int32_t)20, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_58(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_58(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_58(__m256i a, __m256i b) {
  return _vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE __m256i rotate_left_e0(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)10, x, __m256i),
                         mm256_srli_epi64((int32_t)54, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_e0(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_e0(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_e0(__m256i a, __m256i b) {
  return _vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE __m256i rotate_left_63(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)45, x, __m256i),
                         mm256_srli_epi64((int32_t)19, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_63(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_63(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_63(__m256i a, __m256i b) {
  return _vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE __m256i rotate_left_6a(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)2, x, __m256i),
                         mm256_srli_epi64((int32_t)62, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_6a(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_6a(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_6a(__m256i a, __m256i b) {
  return _vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE __m256i rotate_left_ab(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)62, x, __m256i),
                         mm256_srli_epi64((int32_t)2, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_ab(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_ab(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_ab(__m256i a, __m256i b) {
  return _vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE __m256i rotate_left_5b(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)6, x, __m256i),
                         mm256_srli_epi64((int32_t)58, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_5b(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_5b(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_5b(__m256i a, __m256i b) {
  return _vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE __m256i rotate_left_6f(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)43, x, __m256i),
                         mm256_srli_epi64((int32_t)21, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_6f(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_6f(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_6f(__m256i a, __m256i b) {
  return _vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE __m256i rotate_left_62(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)15, x, __m256i),
                         mm256_srli_epi64((int32_t)49, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_62(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_62(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_62(__m256i a, __m256i b) {
  return _vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE __m256i rotate_left_23(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)61, x, __m256i),
                         mm256_srli_epi64((int32_t)3, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_23(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_23(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_23(__m256i a, __m256i b) {
  return _vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE __m256i rotate_left_37(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)28, x, __m256i),
                         mm256_srli_epi64((int32_t)36, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_37(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_37(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_37(__m256i a, __m256i b) {
  return _vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE __m256i rotate_left_bb(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)55, x, __m256i),
                         mm256_srli_epi64((int32_t)9, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_bb(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_bb(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_bb(__m256i a, __m256i b) {
  return _vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE __m256i rotate_left_b9(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)25, x, __m256i),
                         mm256_srli_epi64((int32_t)39, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_b9(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_b9(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_b9(__m256i a, __m256i b) {
  return _vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE __m256i rotate_left_54(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)21, x, __m256i),
                         mm256_srli_epi64((int32_t)43, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_54(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_54(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_54(__m256i a, __m256i b) {
  return _vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE __m256i rotate_left_4c(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)56, x, __m256i),
                         mm256_srli_epi64((int32_t)8, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_4c(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_4c(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_4c(__m256i a, __m256i b) {
  return _vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE __m256i rotate_left_ce(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)27, x, __m256i),
                         mm256_srli_epi64((int32_t)37, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_ce(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_ce(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_ce(__m256i a, __m256i b) {
  return _vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE __m256i rotate_left_77(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)20, x, __m256i),
                         mm256_srli_epi64((int32_t)44, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_77(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_77(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_77(__m256i a, __m256i b) {
  return _vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE __m256i rotate_left_25(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)39, x, __m256i),
                         mm256_srli_epi64((int32_t)25, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_25(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_25(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_25(__m256i a, __m256i b) {
  return _vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE __m256i rotate_left_af(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)8, x, __m256i),
                         mm256_srli_epi64((int32_t)56, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_af(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_af(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_af(__m256i a, __m256i b) {
  return _vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE __m256i rotate_left_fd(__m256i x) {
  return mm256_xor_si256(mm256_slli_epi64((int32_t)14, x, __m256i),
                         mm256_srli_epi64((int32_t)50, x, __m256i));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE __m256i _vxarq_u64_fd(__m256i a, __m256i b) {
  __m256i ab = mm256_xor_si256(a, b);
  return rotate_left_fd(ab);
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
static KRML_MUSTINLINE __m256i xor_and_rotate_ef_fd(__m256i a, __m256i b) {
  return _vxarq_u64_fd(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void theta_rho_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  __m256i c[5U] = {xor5_ef(s->st[0U][0U], s->st[1U][0U], s->st[2U][0U],
                           s->st[3U][0U], s->st[4U][0U]),
                   xor5_ef(s->st[0U][1U], s->st[1U][1U], s->st[2U][1U],
                           s->st[3U][1U], s->st[4U][1U]),
                   xor5_ef(s->st[0U][2U], s->st[1U][2U], s->st[2U][2U],
                           s->st[3U][2U], s->st[4U][2U]),
                   xor5_ef(s->st[0U][3U], s->st[1U][3U], s->st[2U][3U],
                           s->st[3U][3U], s->st[4U][3U]),
                   xor5_ef(s->st[0U][4U], s->st[1U][4U], s->st[2U][4U],
                           s->st[3U][4U], s->st[4U][4U])};
  __m256i uu____0 =
      rotate_left1_and_xor_ef(c[((size_t)0U + (size_t)4U) % (size_t)5U],
                              c[((size_t)0U + (size_t)1U) % (size_t)5U]);
  __m256i uu____1 =
      rotate_left1_and_xor_ef(c[((size_t)1U + (size_t)4U) % (size_t)5U],
                              c[((size_t)1U + (size_t)1U) % (size_t)5U]);
  __m256i uu____2 =
      rotate_left1_and_xor_ef(c[((size_t)2U + (size_t)4U) % (size_t)5U],
                              c[((size_t)2U + (size_t)1U) % (size_t)5U]);
  __m256i uu____3 =
      rotate_left1_and_xor_ef(c[((size_t)3U + (size_t)4U) % (size_t)5U],
                              c[((size_t)3U + (size_t)1U) % (size_t)5U]);
  __m256i t[5U] = {
      uu____0, uu____1, uu____2, uu____3,
      rotate_left1_and_xor_ef(c[((size_t)4U + (size_t)4U) % (size_t)5U],
                              c[((size_t)4U + (size_t)1U) % (size_t)5U])};
  s->st[0U][0U] = xor_ef(s->st[0U][0U], t[0U]);
  s->st[1U][0U] = xor_and_rotate_ef_02(s->st[1U][0U], t[0U]);
  s->st[2U][0U] = xor_and_rotate_ef_ac(s->st[2U][0U], t[0U]);
  s->st[3U][0U] = xor_and_rotate_ef_020(s->st[3U][0U], t[0U]);
  s->st[4U][0U] = xor_and_rotate_ef_a9(s->st[4U][0U], t[0U]);
  s->st[0U][1U] = xor_and_rotate_ef_76(s->st[0U][1U], t[1U]);
  s->st[1U][1U] = xor_and_rotate_ef_58(s->st[1U][1U], t[1U]);
  s->st[2U][1U] = xor_and_rotate_ef_e0(s->st[2U][1U], t[1U]);
  s->st[3U][1U] = xor_and_rotate_ef_63(s->st[3U][1U], t[1U]);
  s->st[4U][1U] = xor_and_rotate_ef_6a(s->st[4U][1U], t[1U]);
  s->st[0U][2U] = xor_and_rotate_ef_ab(s->st[0U][2U], t[2U]);
  s->st[1U][2U] = xor_and_rotate_ef_5b(s->st[1U][2U], t[2U]);
  s->st[2U][2U] = xor_and_rotate_ef_6f(s->st[2U][2U], t[2U]);
  s->st[3U][2U] = xor_and_rotate_ef_62(s->st[3U][2U], t[2U]);
  s->st[4U][2U] = xor_and_rotate_ef_23(s->st[4U][2U], t[2U]);
  s->st[0U][3U] = xor_and_rotate_ef_37(s->st[0U][3U], t[3U]);
  s->st[1U][3U] = xor_and_rotate_ef_bb(s->st[1U][3U], t[3U]);
  s->st[2U][3U] = xor_and_rotate_ef_b9(s->st[2U][3U], t[3U]);
  s->st[3U][3U] = xor_and_rotate_ef_54(s->st[3U][3U], t[3U]);
  s->st[4U][3U] = xor_and_rotate_ef_4c(s->st[4U][3U], t[3U]);
  s->st[0U][4U] = xor_and_rotate_ef_ce(s->st[0U][4U], t[4U]);
  s->st[1U][4U] = xor_and_rotate_ef_77(s->st[1U][4U], t[4U]);
  s->st[2U][4U] = xor_and_rotate_ef_25(s->st[2U][4U], t[4U]);
  s->st[3U][4U] = xor_and_rotate_ef_af(s->st[3U][4U], t[4U]);
  __m256i uu____27 = xor_and_rotate_ef_fd(s->st[4U][4U], t[4U]);
  s->st[4U][4U] = uu____27;
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void pi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  __m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(__m256i[5U]));
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
static KRML_MUSTINLINE void chi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  __m256i old[5U][5U];
  memcpy(old, s->st, (size_t)5U * sizeof(__m256i[5U]));
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0;
      KRML_MAYBE_FOR5(i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i;
                      s->st[i1][j] = and_not_xor_ef(
                          s->st[i1][j], old[i1][(j + (size_t)2U) % (size_t)5U],
                          old[i1][(j + (size_t)1U) % (size_t)5U]);););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void iota_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, size_t i) {
  s->st[0U][0U] = xor_constant_ef(
      s->st[0U][0U], libcrux_sha3_generic_keccak_ROUNDCONSTANTS[i]);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void keccakf1600_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    theta_rho_a6(s);
    pi_a6(s);
    chi_a6(s);
    iota_a6(s, i0);
  }
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
static KRML_MUSTINLINE void absorb_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice blocks[4U]) {
  __m256i(*uu____0)[5U] = s->st;
  Eurydice_slice uu____1[4U];
  memcpy(uu____1, blocks, (size_t)4U * sizeof(Eurydice_slice));
  load_block_ef_5b(uu____0, uu____1);
  keccakf1600_a6(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void load_block_full_5b(__m256i (*s)[5U],
                                               uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  load_block_5b(s, buf);
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
static KRML_MUSTINLINE void load_block_full_ef_5b(__m256i (*a)[5U],
                                                  uint8_t b[4U][200U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[4U][200U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(uint8_t[200U]));
  load_block_full_5b(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void absorb_final_fb(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice last[4U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[4U][200U] = {{0U}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t);
        Eurydice_slice_copy(uu____0, last[i0], uint8_t);
      } blocks[i0][last_len] = 31U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)136U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  __m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  load_block_full_ef_5b(uu____3, uu____4);
  keccakf1600_a6(s);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void store_block_5b(__m256i (*s)[5U],
                                           Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v0l = mm256_permute2x128_si256(
        (int32_t)32,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v1h = mm256_permute2x128_si256(
        (int32_t)32,
        s[((size_t)4U * /* 0 0 2 2 */ i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v2l = mm256_permute2x128_si256(
        (int32_t)49,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v3h =
        mm256_permute2x128_si256((int32_t)49,
                                 s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
                                  [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
                                 s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
                                  [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
                                 __m256i);
    __m256i v0 = mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = mm256_unpackhi_epi64(v2l, v3h);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v0);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v1);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v2);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)136U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
                        s[i0][j0]);
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
    mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t),
                          s[i][j]);
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
static KRML_MUSTINLINE void store_block_full_5b(__m256i (*s)[5U],
                                                uint8_t ret[4U][200U]) {
  uint8_t out0[200U] = {0U};
  uint8_t out1[200U] = {0U};
  uint8_t out2[200U] = {0U};
  uint8_t out3[200U] = {0U};
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, out0, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out1, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out2, uint8_t),
      Eurydice_array_to_slice((size_t)200U, out3, uint8_t)};
  store_block_5b(s, buf);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[200U];
  memcpy(copy_of_out0, out0, (size_t)200U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[200U];
  memcpy(copy_of_out1, out1, (size_t)200U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[200U];
  memcpy(copy_of_out2, out2, (size_t)200U * sizeof(uint8_t));
  uint8_t uu____3[200U];
  memcpy(uu____3, out3, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[0U], copy_of_out0, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[1U], copy_of_out1, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[2U], copy_of_out2, (size_t)200U * sizeof(uint8_t));
  memcpy(ret[3U], uu____3, (size_t)200U * sizeof(uint8_t));
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
static KRML_MUSTINLINE void store_block_full_ef_5b(__m256i (*a)[5U],
                                                   uint8_t ret[4U][200U]) {
  store_block_full_5b(a, ret);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_first_and_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  uint8_t b[4U][200U];
  store_block_full_ef_5b(s->st, b);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_08 lit; lit.start = (size_t)0U;
      lit.end = Eurydice_slice_len(out[i0], uint8_t); Eurydice_slice_copy(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_08),
          uint8_t););
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
static KRML_MUSTINLINE void store_block_ef_5b(__m256i (*a)[5U],
                                              Eurydice_slice b[4U]) {
  store_block_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_first_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  store_block_ef_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_next_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  keccakf1600_a6(s);
  store_block_ef_5b(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 s, Eurydice_slice out[4U]) {
  keccakf1600_a6(&s);
  uint8_t b[4U][200U];
  store_block_full_ef_5b(s.st, b);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice uu____0 = out[i0]; uint8_t *uu____1 = b[i0];
      core_ops_range_Range_08 lit; lit.start = (size_t)0U;
      lit.end = Eurydice_slice_len(out[i0], uint8_t); Eurydice_slice_copy(
          uu____0,
          Eurydice_array_to_subslice((size_t)200U, uu____1, lit, uint8_t,
                                     core_ops_range_Range_08),
          uint8_t););
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void keccak_fb(Eurydice_slice data[4U],
                                      Eurydice_slice out[4U]) {
  libcrux_sha3_generic_keccak_KeccakState_55 s = new_89_a6();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(data[0U], uint8_t) / (size_t)136U; i++) {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_KeccakState_55 *uu____0 = &s;
    /* Passing arrays by value in Rust generates a copy in C */
    Eurydice_slice copy_of_data[4U];
    memcpy(copy_of_data, data, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice ret[4U];
    slice_n_ef(copy_of_data, i0 * (size_t)136U, (size_t)136U, ret);
    absorb_block_97(uu____0, ret);
  }
  size_t rem = Eurydice_slice_len(data[0U], uint8_t) % (size_t)136U;
  libcrux_sha3_generic_keccak_KeccakState_55 *uu____2 = &s;
  /* Passing arrays by value in Rust generates a copy in C */
  Eurydice_slice copy_of_data[4U];
  memcpy(copy_of_data, data, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice ret[4U];
  slice_n_ef(copy_of_data, Eurydice_slice_len(data[0U], uint8_t) - rem, rem,
             ret);
  absorb_final_fb(uu____2, ret);
  size_t outlen = Eurydice_slice_len(out[0U], uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_first_and_last_97(&s, out);
  } else {
    Eurydice_slice_uint8_t_4size_t__x2 uu____4 =
        split_at_mut_n_ef(out, (size_t)136U);
    Eurydice_slice o0[4U];
    memcpy(o0, uu____4.fst, (size_t)4U * sizeof(Eurydice_slice));
    Eurydice_slice o1[4U];
    memcpy(o1, uu____4.snd, (size_t)4U * sizeof(Eurydice_slice));
    squeeze_first_block_97(&s, o0);
    core_ops_range_Range_08 iter =
        core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
            (CLITERAL(core_ops_range_Range_08){.start = (size_t)1U,
                                               .end = blocks}),
            core_ops_range_Range_08, core_ops_range_Range_08);
    while (true) {
      if (core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next(
              &iter, size_t, core_option_Option_08)
              .tag == core_option_None) {
        break;
      } else {
        Eurydice_slice_uint8_t_4size_t__x2 uu____5 =
            split_at_mut_n_ef(o1, (size_t)136U);
        Eurydice_slice o[4U];
        memcpy(o, uu____5.fst, (size_t)4U * sizeof(Eurydice_slice));
        Eurydice_slice orest[4U];
        memcpy(orest, uu____5.snd, (size_t)4U * sizeof(Eurydice_slice));
        squeeze_next_block_97(&s, o);
        memcpy(o1, orest, (size_t)4U * sizeof(Eurydice_slice));
      }
    }
    if (last < outlen) {
      squeeze_last_97(s, o1);
    }
  }
}

/**
 Perform 4 SHAKE256 operations in parallel
*/
void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf0[4U] = {
      /* XXX: These functions could alternatively implement the same with the
         portable implementation #[cfg(feature = "simd128")] { keccakx2::<136,
         0x1fu8>([input0, input1], [out0, out1]); keccakx2::<136,
         0x1fu8>([input2, input3], [out2, out3]); } { keccakx1::<136,
         0x1fu8>([input0], [out0]); keccakx1::<136, 0x1fu8>([input1], [out1]);
         keccakx1::<136, 0x1fu8>([input2], [out2]); keccakx1::<136,
         0x1fu8>([input3], [out3]); } */
      input0,
      input1, input2, input3};
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  keccak_fb(buf0, buf);
}

/**
 Initialise the [`KeccakState`].
*/
libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_avx2_x4_incremental_init(void) {
  return new_89_a6();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void load_block_3a(__m256i (*s)[5U],
                                          Eurydice_slice blocks[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v00 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v10 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v20 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v30 = mm256_loadu_si256_u8(
        Eurydice_slice_subslice2(blocks[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t));
    __m256i v0l = mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = mm256_permute2x128_si256((int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = mm256_permute2x128_si256((int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = mm256_permute2x128_si256((int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = mm256_permute2x128_si256((int32_t)49, v1h, v3h, __m256i);
    s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U] =
        mm256_xor_si256(
            s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U], v0);
    s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)1U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
                         v1);
    s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)2U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
                         v2);
    s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
     [((size_t)4U * i0 + (size_t)3U) % (size_t)5U] =
         mm256_xor_si256(s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
                          [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
                         v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
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
  __m256i u = mm256_loadu_si256_u8(core_array___Array_T__N__23__as_slice(
      (size_t)32U, u8s, uint8_t, Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  s[i0][j0] = mm256_xor_si256(s[i0][j0], u);
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
    __m256i u0 = mm256_loadu_si256_u8(core_array___Array_T__N__23__as_slice(
        (size_t)32U, u8s0, uint8_t, Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    s[i][j] = mm256_xor_si256(s[i][j], u0);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block_full
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void load_block_full_3a(__m256i (*s)[5U],
                                               uint8_t blocks[4U][200U]) {
  Eurydice_slice buf[4U] = {
      Eurydice_array_to_slice((size_t)200U, blocks[0U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[1U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[2U], uint8_t),
      Eurydice_array_to_slice((size_t)200U, blocks[3U], uint8_t)};
  load_block_3a(s, buf);
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
static KRML_MUSTINLINE void load_block_full_ef_3a(__m256i (*a)[5U],
                                                  uint8_t b[4U][200U]) {
  __m256i(*uu____0)[5U] = a;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_b[4U][200U];
  memcpy(copy_of_b, b, (size_t)4U * sizeof(uint8_t[200U]));
  load_block_full_3a(uu____0, copy_of_b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void absorb_final_fb0(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice last[4U]) {
  size_t last_len = Eurydice_slice_len(last[0U], uint8_t);
  uint8_t blocks[4U][200U] = {{0U}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (last_len > (size_t)0U) {
        Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
            blocks[i0], (size_t)0U, last_len, uint8_t);
        Eurydice_slice_copy(uu____0, last[i0], uint8_t);
      } blocks[i0][last_len] = 31U;
      size_t uu____1 = i0; size_t uu____2 = (size_t)168U - (size_t)1U;
      blocks[uu____1][uu____2] = (uint32_t)blocks[uu____1][uu____2] | 128U;);
  __m256i(*uu____3)[5U] = s->st;
  uint8_t uu____4[4U][200U];
  memcpy(uu____4, blocks, (size_t)4U * sizeof(uint8_t[200U]));
  load_block_full_ef_3a(uu____3, uu____4);
  keccakf1600_a6(s);
}

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  absorb_final_fb0(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void store_block_3a(__m256i (*s)[5U],
                                           Eurydice_slice out[4U]) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i0 = i;
    __m256i v0l = mm256_permute2x128_si256(
        (int32_t)32,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v1h = mm256_permute2x128_si256(
        (int32_t)32,
        s[((size_t)4U * /* 0 0 2 2 */ i0 + (size_t)1U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
        __m256i);
    __m256i v2l = mm256_permute2x128_si256(
        (int32_t)49,
        s[(size_t)4U * i0 / (size_t)5U][(size_t)4U * i0 % (size_t)5U],
        s[((size_t)4U * i0 + (size_t)2U) / (size_t)5U]
         [((size_t)4U * i0 + (size_t)2U) % (size_t)5U],
        __m256i);
    __m256i v3h =
        mm256_permute2x128_si256((int32_t)49,
                                 s[((size_t)4U * i0 + (size_t)1U) / (size_t)5U]
                                  [((size_t)4U * i0 + (size_t)1U) % (size_t)5U],
                                 s[((size_t)4U * i0 + (size_t)3U) / (size_t)5U]
                                  [((size_t)4U * i0 + (size_t)3U) % (size_t)5U],
                                 __m256i);
    __m256i v0 = mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = mm256_unpackhi_epi64(v2l, v3h);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[0U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v0);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[1U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v1);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[2U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v2);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice2(out[3U], (size_t)32U * i0,
                                 (size_t)32U * (i0 + (size_t)1U), uint8_t),
        v3);
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = (size_t)32U * ((size_t)168U / (size_t)32U);
  uint8_t u8s[32U] = {0U};
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, u8s, uint8_t),
                        s[i0][j0]);
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
    mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, u8s0, uint8_t),
                          s[i][j]);
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
static KRML_MUSTINLINE void store_block_ef_3a(__m256i (*a)[5U],
                                              Eurydice_slice b[4U]) {
  store_block_3a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_next_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  keccakf1600_a6(s);
  store_block_ef_3a(s->st, out);
}

/**
 Squeeze another block
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  squeeze_next_block_970(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  store_block_ef_3a(s->st, out);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_three_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_first_block_970(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o2[4U];
  memcpy(o2, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_next_block_970(s, o1);
  squeeze_next_block_970(s, o2);
}

/**
 Squeeze three blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  squeeze_first_three_blocks_97(s, buf);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_five_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]) {
  Eurydice_slice_uint8_t_4size_t__x2 uu____0 =
      split_at_mut_n_ef(out, (size_t)168U);
  Eurydice_slice o0[4U];
  memcpy(o0, uu____0.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o10[4U];
  memcpy(o10, uu____0.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_first_block_970(s, o0);
  Eurydice_slice_uint8_t_4size_t__x2 uu____1 =
      split_at_mut_n_ef(o10, (size_t)168U);
  Eurydice_slice o1[4U];
  memcpy(o1, uu____1.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o20[4U];
  memcpy(o20, uu____1.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_next_block_970(s, o1);
  Eurydice_slice_uint8_t_4size_t__x2 uu____2 =
      split_at_mut_n_ef(o20, (size_t)168U);
  Eurydice_slice o2[4U];
  memcpy(o2, uu____2.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o30[4U];
  memcpy(o30, uu____2.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_next_block_970(s, o2);
  Eurydice_slice_uint8_t_4size_t__x2 uu____3 =
      split_at_mut_n_ef(o30, (size_t)168U);
  Eurydice_slice o3[4U];
  memcpy(o3, uu____3.fst, (size_t)4U * sizeof(Eurydice_slice));
  Eurydice_slice o4[4U];
  memcpy(o4, uu____3.snd, (size_t)4U * sizeof(Eurydice_slice));
  squeeze_next_block_970(s, o3);
  squeeze_next_block_970(s, o4);
}

/**
 Squeeze five blocks
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  squeeze_first_five_blocks_97(s, buf);
}

/**
 Absorb
*/
KRML_MUSTINLINE void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice data0,
    Eurydice_slice data1, Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_slice buf[4U] = {data0, data1, data2, data3};
  absorb_final_fb(s, buf);
}

/**
 Squeeze block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  squeeze_first_block_97(s, buf);
}

/**
 Squeeze next block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out0,
    Eurydice_slice out1, Eurydice_slice out2, Eurydice_slice out3) {
  Eurydice_slice buf[4U] = {out0, out1, out2, out3};
  squeeze_next_block_97(s, buf);
}
