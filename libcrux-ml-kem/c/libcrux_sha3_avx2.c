/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9664988fc6405409f3815686f7284fb32e8d9b8e
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */

#include "libcrux_sha3_avx2.h"

#include "internal/libcrux_core.h"
#include "libcrux_core.h"
#include "libcrux_sha3_portable.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i zero_b0(void) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i xor5_b0(__m256i a, __m256i b, __m256i c,
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i rotate_left1_and_xor_b0(__m256i a, __m256i b) {
  return _vrax1q_u64(a, b);
}

static KRML_MUSTINLINE __m256i _vbcaxq_u64(__m256i a, __m256i b, __m256i c) {
  return mm256_xor_si256(a, mm256_andnot_si256(c, b));
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i and_not_xor_b0(__m256i a, __m256i b, __m256i c) {
  return _vbcaxq_u64(a, b, c);
}

static KRML_MUSTINLINE __m256i _veorq_n_u64(__m256i a, uint64_t c) {
  __m256i c0 = mm256_set1_epi64x((int64_t)c);
  return mm256_xor_si256(a, c0);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i xor_constant_b0(__m256i a, uint64_t c) {
  return _veorq_n_u64(a, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
static KRML_MUSTINLINE __m256i xor_b0(__m256i a, __m256i b) {
  return mm256_xor_si256(a, b);
}

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
static KRML_MUSTINLINE Eurydice_arr_05 new_80_a6(void) {
  Eurydice_arr_05 lit;
  __m256i repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression[i] = zero_b0();
  }
  memcpy(lit.data, repeat_expression, (size_t)25U * sizeof(__m256i));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void set_ij_a6(Eurydice_arr_05 *arr, size_t i, size_t j,
                                      __m256i value) {
  arr->data[(size_t)5U * j + i] = value;
}

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE __m256i *get_ij_a6(Eurydice_arr_05 *arr, size_t i,
                                          size_t j) {
  return &arr->data[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void load_block_5b(Eurydice_arr_05 *state,
                                          Eurydice_arr_d9 *blocks,
                                          size_t offset) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[0U], start, start + (size_t)32U, uint8_t *));
    __m256i v10 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[1U], start, start + (size_t)32U, uint8_t *));
    __m256i v20 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[2U], start, start + (size_t)32U, uint8_t *));
    __m256i v30 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[3U], start, start + (size_t)32U, uint8_t *));
    __m256i v0l = mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = mm256_permute2x128_si256((int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = mm256_permute2x128_si256((int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = mm256_permute2x128_si256((int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = mm256_permute2x128_si256((int32_t)49, v1h, v3h, __m256i);
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    set_ij_a6(state, i0, j0, mm256_xor_si256(get_ij_a6(state, i0, j0)[0U], v0));
    set_ij_a6(state, i1, j1, mm256_xor_si256(get_ij_a6(state, i1, j1)[0U], v1));
    set_ij_a6(state, i2, j2, mm256_xor_si256(get_ij_a6(state, i2, j2)[0U], v2));
    set_ij_a6(state, i3, j3, mm256_xor_si256(get_ij_a6(state, i3, j3)[0U], v3));
  }
  size_t rem = (size_t)136U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)136U / (size_t)32U);
  Eurydice_arr_60 u8s = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)0U, (size_t)8U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)8U, (size_t)16U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)16U, (size_t)24U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[2U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)24U, (size_t)32U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[3U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  __m256i u = mm256_loadu_si256_u8(core_array___Array_T__N___as_slice(
      (size_t)32U, &u8s, uint8_t, Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)136U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)136U / (size_t)32U) % (size_t)5U;
  set_ij_a6(state, i0, j0, mm256_xor_si256(get_ij_a6(state, i0, j0)[0U], u));
  if (rem == (size_t)16U) {
    Eurydice_arr_60 u8s0 = {.data = {0U}};
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)0U, (size_t)8U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)8U, (size_t)16U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)16U, (size_t)24U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)24U, (size_t)32U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    __m256i u0 = mm256_loadu_si256_u8(core_array___Array_T__N___as_slice(
        (size_t)32U, &u8s0, uint8_t, Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)136U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    set_ij_a6(state, i, j, mm256_xor_si256(get_ij_a6(state, i, j)[0U], u0));
  }
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
static void load_block_8f_5b(Eurydice_arr_05 *self, Eurydice_arr_d9 *input,
                             size_t start) {
  load_block_5b(self, input, start);
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
static __m256i *index_c2_a6(Eurydice_arr_05 *self, size_t_x2 index) {
  return get_ij_a6(self, index.fst, index.snd);
}

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $5size_t
*/
typedef struct arr_c0_s {
  __m256i data[5U];
} arr_c0;

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
static void set_80_a6(Eurydice_arr_05 *self, size_t i, size_t j, __m256i v) {
  set_ij_a6(self, i, j, v);
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_02(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_ac(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_020(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_a9(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_76(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_58(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_e0(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_63(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_6a(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_ab(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_5b(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_6f(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_62(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_23(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_37(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_bb(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_b9(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_54(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_4c(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_ce(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_77(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_25(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_af(__m256i a, __m256i b) {
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
This function found in impl {libcrux_sha3::traits::KeccakItem<4usize> for
core::core_arch::x86::__m256i}
*/
/**
A monomorphic instance of libcrux_sha3.simd.avx2.xor_and_rotate_b0
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE __m256i xor_and_rotate_b0_fd(__m256i a, __m256i b) {
  return _vxarq_u64_fd(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
static KRML_MUSTINLINE void theta_rho_80_a6(Eurydice_arr_05 *self) {
  arr_c0 c = {
      .data = {
          xor5_b0(
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)0U, .snd = (size_t)0U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)1U, .snd = (size_t)0U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)2U, .snd = (size_t)0U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)3U, .snd = (size_t)0U}))[0U],
              index_c2_a6(self,
                          (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                    .snd = (size_t)0U}))[0U]),
          xor5_b0(
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)0U, .snd = (size_t)1U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)1U, .snd = (size_t)1U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)2U, .snd = (size_t)1U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)3U, .snd = (size_t)1U}))[0U],
              index_c2_a6(self,
                          (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                    .snd = (size_t)1U}))[0U]),
          xor5_b0(
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)0U, .snd = (size_t)2U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)1U, .snd = (size_t)2U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)2U, .snd = (size_t)2U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)3U, .snd = (size_t)2U}))[0U],
              index_c2_a6(self,
                          (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                    .snd = (size_t)2U}))[0U]),
          xor5_b0(
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)0U, .snd = (size_t)3U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)1U, .snd = (size_t)3U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)2U, .snd = (size_t)3U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)3U, .snd = (size_t)3U}))[0U],
              index_c2_a6(self,
                          (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                    .snd = (size_t)3U}))[0U]),
          xor5_b0(
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)0U, .snd = (size_t)4U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)1U, .snd = (size_t)4U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)2U, .snd = (size_t)4U}))[0U],
              index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                    .fst = (size_t)3U, .snd = (size_t)4U}))[0U],
              index_c2_a6(self,
                          (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                    .snd = (size_t)4U}))[0U])}};
  __m256i uu____0 =
      rotate_left1_and_xor_b0(c.data[((size_t)0U + (size_t)4U) % (size_t)5U],
                              c.data[((size_t)0U + (size_t)1U) % (size_t)5U]);
  __m256i uu____1 =
      rotate_left1_and_xor_b0(c.data[((size_t)1U + (size_t)4U) % (size_t)5U],
                              c.data[((size_t)1U + (size_t)1U) % (size_t)5U]);
  __m256i uu____2 =
      rotate_left1_and_xor_b0(c.data[((size_t)2U + (size_t)4U) % (size_t)5U],
                              c.data[((size_t)2U + (size_t)1U) % (size_t)5U]);
  __m256i uu____3 =
      rotate_left1_and_xor_b0(c.data[((size_t)3U + (size_t)4U) % (size_t)5U],
                              c.data[((size_t)3U + (size_t)1U) % (size_t)5U]);
  arr_c0 t = {.data = {uu____0, uu____1, uu____2, uu____3,
                       rotate_left1_and_xor_b0(
                           c.data[((size_t)4U + (size_t)4U) % (size_t)5U],
                           c.data[((size_t)4U + (size_t)1U) % (size_t)5U])}};
  set_80_a6(
      self, (size_t)0U, (size_t)0U,
      xor_b0(index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                   .fst = (size_t)0U, .snd = (size_t)0U}))[0U],
             t.data[0U]));
  Eurydice_arr_05 *uu____4 = self;
  set_80_a6(
      uu____4, (size_t)1U, (size_t)0U,
      xor_and_rotate_b0_02(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                                      .snd = (size_t)0U}))[0U],
          t.data[0U]));
  Eurydice_arr_05 *uu____5 = self;
  set_80_a6(
      uu____5, (size_t)2U, (size_t)0U,
      xor_and_rotate_b0_ac(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                                      .snd = (size_t)0U}))[0U],
          t.data[0U]));
  Eurydice_arr_05 *uu____6 = self;
  set_80_a6(
      uu____6, (size_t)3U, (size_t)0U,
      xor_and_rotate_b0_020(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                                      .snd = (size_t)0U}))[0U],
          t.data[0U]));
  Eurydice_arr_05 *uu____7 = self;
  set_80_a6(
      uu____7, (size_t)4U, (size_t)0U,
      xor_and_rotate_b0_a9(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                      .snd = (size_t)0U}))[0U],
          t.data[0U]));
  Eurydice_arr_05 *uu____8 = self;
  set_80_a6(
      uu____8, (size_t)0U, (size_t)1U,
      xor_and_rotate_b0_76(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                                      .snd = (size_t)1U}))[0U],
          t.data[1U]));
  Eurydice_arr_05 *uu____9 = self;
  set_80_a6(
      uu____9, (size_t)1U, (size_t)1U,
      xor_and_rotate_b0_58(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                                      .snd = (size_t)1U}))[0U],
          t.data[1U]));
  Eurydice_arr_05 *uu____10 = self;
  set_80_a6(
      uu____10, (size_t)2U, (size_t)1U,
      xor_and_rotate_b0_e0(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                                      .snd = (size_t)1U}))[0U],
          t.data[1U]));
  Eurydice_arr_05 *uu____11 = self;
  set_80_a6(
      uu____11, (size_t)3U, (size_t)1U,
      xor_and_rotate_b0_63(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                                      .snd = (size_t)1U}))[0U],
          t.data[1U]));
  Eurydice_arr_05 *uu____12 = self;
  set_80_a6(
      uu____12, (size_t)4U, (size_t)1U,
      xor_and_rotate_b0_6a(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                      .snd = (size_t)1U}))[0U],
          t.data[1U]));
  Eurydice_arr_05 *uu____13 = self;
  set_80_a6(
      uu____13, (size_t)0U, (size_t)2U,
      xor_and_rotate_b0_ab(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                                      .snd = (size_t)2U}))[0U],
          t.data[2U]));
  Eurydice_arr_05 *uu____14 = self;
  set_80_a6(
      uu____14, (size_t)1U, (size_t)2U,
      xor_and_rotate_b0_5b(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                                      .snd = (size_t)2U}))[0U],
          t.data[2U]));
  Eurydice_arr_05 *uu____15 = self;
  set_80_a6(
      uu____15, (size_t)2U, (size_t)2U,
      xor_and_rotate_b0_6f(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                                      .snd = (size_t)2U}))[0U],
          t.data[2U]));
  Eurydice_arr_05 *uu____16 = self;
  set_80_a6(
      uu____16, (size_t)3U, (size_t)2U,
      xor_and_rotate_b0_62(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                                      .snd = (size_t)2U}))[0U],
          t.data[2U]));
  Eurydice_arr_05 *uu____17 = self;
  set_80_a6(
      uu____17, (size_t)4U, (size_t)2U,
      xor_and_rotate_b0_23(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                      .snd = (size_t)2U}))[0U],
          t.data[2U]));
  Eurydice_arr_05 *uu____18 = self;
  set_80_a6(
      uu____18, (size_t)0U, (size_t)3U,
      xor_and_rotate_b0_37(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                                      .snd = (size_t)3U}))[0U],
          t.data[3U]));
  Eurydice_arr_05 *uu____19 = self;
  set_80_a6(
      uu____19, (size_t)1U, (size_t)3U,
      xor_and_rotate_b0_bb(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                                      .snd = (size_t)3U}))[0U],
          t.data[3U]));
  Eurydice_arr_05 *uu____20 = self;
  set_80_a6(
      uu____20, (size_t)2U, (size_t)3U,
      xor_and_rotate_b0_b9(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                                      .snd = (size_t)3U}))[0U],
          t.data[3U]));
  Eurydice_arr_05 *uu____21 = self;
  set_80_a6(
      uu____21, (size_t)3U, (size_t)3U,
      xor_and_rotate_b0_54(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                                      .snd = (size_t)3U}))[0U],
          t.data[3U]));
  Eurydice_arr_05 *uu____22 = self;
  set_80_a6(
      uu____22, (size_t)4U, (size_t)3U,
      xor_and_rotate_b0_4c(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                      .snd = (size_t)3U}))[0U],
          t.data[3U]));
  Eurydice_arr_05 *uu____23 = self;
  set_80_a6(
      uu____23, (size_t)0U, (size_t)4U,
      xor_and_rotate_b0_ce(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                                      .snd = (size_t)4U}))[0U],
          t.data[4U]));
  Eurydice_arr_05 *uu____24 = self;
  set_80_a6(
      uu____24, (size_t)1U, (size_t)4U,
      xor_and_rotate_b0_77(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)1U,
                                                      .snd = (size_t)4U}))[0U],
          t.data[4U]));
  Eurydice_arr_05 *uu____25 = self;
  set_80_a6(
      uu____25, (size_t)2U, (size_t)4U,
      xor_and_rotate_b0_25(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)2U,
                                                      .snd = (size_t)4U}))[0U],
          t.data[4U]));
  Eurydice_arr_05 *uu____26 = self;
  set_80_a6(
      uu____26, (size_t)3U, (size_t)4U,
      xor_and_rotate_b0_af(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)3U,
                                                      .snd = (size_t)4U}))[0U],
          t.data[4U]));
  Eurydice_arr_05 *uu____27 = self;
  set_80_a6(
      uu____27, (size_t)4U, (size_t)4U,
      xor_and_rotate_b0_fd(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)4U,
                                                      .snd = (size_t)4U}))[0U],
          t.data[4U]));
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
static KRML_MUSTINLINE void pi_80_a6(Eurydice_arr_05 *self) {
  Eurydice_arr_05 old = self[0U];
  set_80_a6(self, (size_t)1U, (size_t)0U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)0U, .snd = (size_t)3U}))[0U]);
  set_80_a6(self, (size_t)2U, (size_t)0U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)0U, .snd = (size_t)1U}))[0U]);
  set_80_a6(self, (size_t)3U, (size_t)0U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)0U, .snd = (size_t)4U}))[0U]);
  set_80_a6(self, (size_t)4U, (size_t)0U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)0U, .snd = (size_t)2U}))[0U]);
  set_80_a6(self, (size_t)0U, (size_t)1U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)1U, .snd = (size_t)1U}))[0U]);
  set_80_a6(self, (size_t)1U, (size_t)1U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)1U, .snd = (size_t)4U}))[0U]);
  set_80_a6(self, (size_t)2U, (size_t)1U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)1U, .snd = (size_t)2U}))[0U]);
  set_80_a6(self, (size_t)3U, (size_t)1U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)1U, .snd = (size_t)0U}))[0U]);
  set_80_a6(self, (size_t)4U, (size_t)1U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)1U, .snd = (size_t)3U}))[0U]);
  set_80_a6(self, (size_t)0U, (size_t)2U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)2U, .snd = (size_t)2U}))[0U]);
  set_80_a6(self, (size_t)1U, (size_t)2U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)2U, .snd = (size_t)0U}))[0U]);
  set_80_a6(self, (size_t)2U, (size_t)2U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)2U, .snd = (size_t)3U}))[0U]);
  set_80_a6(self, (size_t)3U, (size_t)2U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)2U, .snd = (size_t)1U}))[0U]);
  set_80_a6(self, (size_t)4U, (size_t)2U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)2U, .snd = (size_t)4U}))[0U]);
  set_80_a6(self, (size_t)0U, (size_t)3U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)3U, .snd = (size_t)3U}))[0U]);
  set_80_a6(self, (size_t)1U, (size_t)3U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)3U, .snd = (size_t)1U}))[0U]);
  set_80_a6(self, (size_t)2U, (size_t)3U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)3U, .snd = (size_t)4U}))[0U]);
  set_80_a6(self, (size_t)3U, (size_t)3U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)3U, .snd = (size_t)2U}))[0U]);
  set_80_a6(self, (size_t)4U, (size_t)3U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)3U, .snd = (size_t)0U}))[0U]);
  set_80_a6(self, (size_t)0U, (size_t)4U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)4U, .snd = (size_t)4U}))[0U]);
  set_80_a6(self, (size_t)1U, (size_t)4U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)4U, .snd = (size_t)2U}))[0U]);
  set_80_a6(self, (size_t)2U, (size_t)4U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)4U, .snd = (size_t)0U}))[0U]);
  set_80_a6(self, (size_t)3U, (size_t)4U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)4U, .snd = (size_t)3U}))[0U]);
  set_80_a6(self, (size_t)4U, (size_t)4U,
            index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                  .fst = (size_t)4U, .snd = (size_t)1U}))[0U]);
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
static KRML_MUSTINLINE void chi_80_a6(Eurydice_arr_05 *self) {
  Eurydice_arr_05 old = self[0U];
  KRML_MAYBE_FOR5(
      i0, (size_t)0U, (size_t)5U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR5(
          i, (size_t)0U, (size_t)5U, (size_t)1U, size_t j = i; set_80_a6(
              self, i1, j,
              and_not_xor_b0(index_c2_a6(self, (KRML_CLITERAL(size_t_x2){
                                                   .fst = i1, .snd = j}))[0U],
                             index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                                   .fst = i1,
                                                   .snd = (j + (size_t)2U) %
                                                          (size_t)5U}))[0U],
                             index_c2_a6(&old, (KRML_CLITERAL(size_t_x2){
                                                   .fst = i1,
                                                   .snd = (j + (size_t)1U) %
                                                          (size_t)5U}))[0U])););
      continue;);
  return;
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
static KRML_MUSTINLINE void iota_80_a6(Eurydice_arr_05 *self, size_t i) {
  set_80_a6(
      self, (size_t)0U, (size_t)0U,
      xor_constant_b0(
          index_c2_a6(self, (KRML_CLITERAL(size_t_x2){.fst = (size_t)0U,
                                                      .snd = (size_t)0U}))[0U],
          LIBCRUX_SHA3_GENERIC_KECCAK_CONSTANTS_ROUNDCONSTANTS.data[i]));
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
static KRML_MUSTINLINE void keccakf1600_80_a6(Eurydice_arr_05 *self) {
  for (size_t i = (size_t)0U; i < (size_t)24U; i++) {
    size_t i0 = i;
    theta_rho_80_a6(self);
    pi_80_a6(self);
    chi_80_a6(self);
    iota_80_a6(self, i0);
  }
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
static KRML_MUSTINLINE void absorb_block_80_97(Eurydice_arr_05 *self,
                                               Eurydice_arr_d9 *blocks,
                                               size_t start) {
  load_block_8f_5b(self, blocks, start);
  keccakf1600_80_a6(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void load_last_ad(Eurydice_arr_05 *state,
                                         Eurydice_arr_d9 *blocks, size_t start,
                                         size_t len) {
  Eurydice_arr_91 buffers = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice_copy(Eurydice_array_to_subslice3(
                              &buffers.data[i0], (size_t)0U, len, uint8_t *),
                          Eurydice_slice_subslice3(blocks->data[i0], start,
                                                   start + len, uint8_t *),
                          uint8_t);
      buffers.data[i0].data[len] = 31U; size_t uu____0 = i0;
      size_t uu____1 = (size_t)136U - (size_t)1U;
      buffers.data[uu____0].data[uu____1] =
          (uint32_t)buffers.data[uu____0].data[uu____1] | 128U;);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d9 lvalue = {
      .data = {
          Eurydice_array_to_slice((size_t)136U, buffers.data, uint8_t),
          Eurydice_array_to_slice((size_t)136U, &buffers.data[1U], uint8_t),
          Eurydice_array_to_slice((size_t)136U, &buffers.data[2U], uint8_t),
          Eurydice_array_to_slice((size_t)136U, &buffers.data[3U], uint8_t)}};
  load_block_5b(state, &lvalue, (size_t)0U);
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
static void load_last_8f_ad(Eurydice_arr_05 *self, Eurydice_arr_d9 *input,
                            size_t start, size_t len) {
  load_last_ad(self, input, start, len);
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
static KRML_MUSTINLINE void absorb_final_80_fb(Eurydice_arr_05 *self,
                                               Eurydice_arr_d9 *last,
                                               size_t start, size_t len) {
  load_last_8f_ad(self, last, start, len);
  keccakf1600_80_a6(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void store_block_5b(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3, size_t start, size_t len) {
  size_t chunks = len / (size_t)32U;
  for (size_t i = (size_t)0U; i < chunks; i++) {
    size_t i4 = i;
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    __m256i v0l =
        mm256_permute2x128_si256((int32_t)32, get_ij_a6(s, i0, j0)[0U],
                                 get_ij_a6(s, i2, j2)[0U], __m256i);
    __m256i v1h =
        mm256_permute2x128_si256((int32_t)32, get_ij_a6(s, i1, j1)[0U],
                                 get_ij_a6(s, i3, j3)[0U], __m256i);
    __m256i v2l =
        mm256_permute2x128_si256((int32_t)49, get_ij_a6(s, i0, j0)[0U],
                                 get_ij_a6(s, i2, j2)[0U], __m256i);
    __m256i v3h =
        mm256_permute2x128_si256((int32_t)49, get_ij_a6(s, i1, j1)[0U],
                                 get_ij_a6(s, i3, j3)[0U], __m256i);
    __m256i v0 = mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = mm256_unpackhi_epi64(v2l, v3h);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out0, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v0);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out1, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v1);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out2, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v2);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out3, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v3);
    continue;
  }
  size_t rem = len % (size_t)32U;
  if (rem > (size_t)0U) {
    size_t start0 = start + (size_t)32U * chunks;
    Eurydice_arr_60 u8s = {.data = {0U}};
    size_t chunks8 = rem / (size_t)8U;
    for (size_t i0 = (size_t)0U; i0 < chunks8; i0++) {
      size_t k = i0;
      size_t i = ((size_t)4U * chunks + k) / (size_t)5U;
      size_t j = ((size_t)4U * chunks + k) % (size_t)5U;
      mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, &u8s, uint8_t),
                            get_ij_a6(s, i, j)[0U]);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out0, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)0U, (size_t)8U, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out1, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)8U, (size_t)16U, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out2, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)16U, (size_t)24U,
                                      uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out3, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)24U, (size_t)32U,
                                      uint8_t *),
          uint8_t);
    }
    size_t rem8 = rem % (size_t)8U;
    if (rem8 > (size_t)0U) {
      size_t i = ((size_t)4U * chunks + chunks8) / (size_t)5U;
      size_t j = ((size_t)4U * chunks + chunks8) % (size_t)5U;
      mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, &u8s, uint8_t),
                            get_ij_a6(s, i, j)[0U]);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out0, start0 + len - rem8, start0 + len,
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)0U, rem, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out1, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)8U, (size_t)8U + rem, uint8_t *),
                          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out2, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)16U, (size_t)16U + rem, uint8_t *),
                          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out3, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)24U, (size_t)24U + rem, uint8_t *),
                          uint8_t);
    }
  }
  return;
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
A monomorphic instance of libcrux_sha3.simd.avx2.squeeze_17
with const generics
- RATE= 136
*/
static void squeeze_17_5b(Eurydice_arr_05 *self, Eurydice_slice out0,
                          Eurydice_slice out1, Eurydice_slice out2,
                          Eurydice_slice out3, size_t start, size_t len) {
  store_block_5b(self, out0, out1, out2, out3, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd256.keccak4
with const generics
- RATE= 136
- DELIM= 31
*/
static inline void keccak4_ad(Eurydice_arr_d9 *data, Eurydice_slice out0,
                              Eurydice_slice out1, Eurydice_slice out2,
                              Eurydice_slice out3) {
  Eurydice_arr_05 s = new_80_a6();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++) {
    size_t i0 = i;
    absorb_block_80_97(&s, data, i0 * (size_t)136U);
    continue;
  }
  size_t rem = data_len % (size_t)136U;
  absorb_final_80_fb(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U) {
    squeeze_17_5b(&s, out0, out1, out2, out3, (size_t)0U, outlen);
    return;
  } else {
    squeeze_17_5b(&s, out0, out1, out2, out3, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++) {
      size_t i0 = i;
      keccakf1600_80_a6(&s);
      squeeze_17_5b(&s, out0, out1, out2, out3, i0 * (size_t)136U,
                    (size_t)136U);
    }
    if (last < outlen) {
      keccakf1600_80_a6(&s);
      squeeze_17_5b(&s, out0, out1, out2, out3, last, outlen - last);
    }
    return;
  }
}

/**
 Perform 4 SHAKE256 operations in parallel
*/
void libcrux_sha3_avx2_x4_shake256(Eurydice_slice input0, Eurydice_slice input1,
                                   Eurydice_slice input2, Eurydice_slice input3,
                                   Eurydice_slice out0, Eurydice_slice out1,
                                   Eurydice_slice out2, Eurydice_slice out3) {
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d9 lvalue = {.data = {input0, input1, input2, input3}};
  keccak4_ad(&lvalue, out0, out1, out2, out3);
}

/**
 Initialise the [`KeccakState`].
*/
Eurydice_arr_05 libcrux_sha3_avx2_x4_incremental_init(void) {
  return new_80_a6();
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void load_block_3a(Eurydice_arr_05 *state,
                                          Eurydice_arr_d9 *blocks,
                                          size_t offset) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)32U; i++) {
    size_t i4 = i;
    size_t start = offset + (size_t)32U * i4;
    __m256i v00 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[0U], start, start + (size_t)32U, uint8_t *));
    __m256i v10 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[1U], start, start + (size_t)32U, uint8_t *));
    __m256i v20 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[2U], start, start + (size_t)32U, uint8_t *));
    __m256i v30 = mm256_loadu_si256_u8(Eurydice_slice_subslice3(
        blocks->data[3U], start, start + (size_t)32U, uint8_t *));
    __m256i v0l = mm256_unpacklo_epi64(v00, v10);
    __m256i v1h = mm256_unpackhi_epi64(v00, v10);
    __m256i v2l = mm256_unpacklo_epi64(v20, v30);
    __m256i v3h = mm256_unpackhi_epi64(v20, v30);
    __m256i v0 = mm256_permute2x128_si256((int32_t)32, v0l, v2l, __m256i);
    __m256i v1 = mm256_permute2x128_si256((int32_t)32, v1h, v3h, __m256i);
    __m256i v2 = mm256_permute2x128_si256((int32_t)49, v0l, v2l, __m256i);
    __m256i v3 = mm256_permute2x128_si256((int32_t)49, v1h, v3h, __m256i);
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    set_ij_a6(state, i0, j0, mm256_xor_si256(get_ij_a6(state, i0, j0)[0U], v0));
    set_ij_a6(state, i1, j1, mm256_xor_si256(get_ij_a6(state, i1, j1)[0U], v1));
    set_ij_a6(state, i2, j2, mm256_xor_si256(get_ij_a6(state, i2, j2)[0U], v2));
    set_ij_a6(state, i3, j3, mm256_xor_si256(get_ij_a6(state, i3, j3)[0U], v3));
  }
  size_t rem = (size_t)168U % (size_t)32U;
  size_t start = offset + (size_t)32U * ((size_t)168U / (size_t)32U);
  Eurydice_arr_60 u8s = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)0U, (size_t)8U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)8U, (size_t)16U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)16U, (size_t)24U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[2U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(&u8s, (size_t)24U, (size_t)32U, uint8_t *),
      Eurydice_slice_subslice3(blocks->data[3U], start, start + (size_t)8U,
                               uint8_t *),
      uint8_t);
  __m256i u = mm256_loadu_si256_u8(core_array___Array_T__N___as_slice(
      (size_t)32U, &u8s, uint8_t, Eurydice_slice));
  size_t i0 = (size_t)4U * ((size_t)168U / (size_t)32U) / (size_t)5U;
  size_t j0 = (size_t)4U * ((size_t)168U / (size_t)32U) % (size_t)5U;
  set_ij_a6(state, i0, j0, mm256_xor_si256(get_ij_a6(state, i0, j0)[0U], u));
  if (rem == (size_t)16U) {
    Eurydice_arr_60 u8s0 = {.data = {0U}};
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)0U, (size_t)8U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[0U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)8U, (size_t)16U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[1U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)16U, (size_t)24U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[2U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&u8s0, (size_t)24U, (size_t)32U, uint8_t *),
        Eurydice_slice_subslice3(blocks->data[3U], start + (size_t)8U,
                                 start + (size_t)16U, uint8_t *),
        uint8_t);
    __m256i u0 = mm256_loadu_si256_u8(core_array___Array_T__N___as_slice(
        (size_t)32U, &u8s0, uint8_t, Eurydice_slice));
    size_t i =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) / (size_t)5U;
    size_t j =
        ((size_t)4U * ((size_t)168U / (size_t)32U) + (size_t)1U) % (size_t)5U;
    set_ij_a6(state, i, j, mm256_xor_si256(get_ij_a6(state, i, j)[0U], u0));
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void load_last_c6(Eurydice_arr_05 *state,
                                         Eurydice_arr_d9 *blocks, size_t start,
                                         size_t len) {
  Eurydice_arr_a6 buffers = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_slice_copy(Eurydice_array_to_subslice3(
                              &buffers.data[i0], (size_t)0U, len, uint8_t *),
                          Eurydice_slice_subslice3(blocks->data[i0], start,
                                                   start + len, uint8_t *),
                          uint8_t);
      buffers.data[i0].data[len] = 31U; size_t uu____0 = i0;
      size_t uu____1 = (size_t)168U - (size_t)1U;
      buffers.data[uu____0].data[uu____1] =
          (uint32_t)buffers.data[uu____0].data[uu____1] | 128U;);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d9 lvalue = {
      .data = {
          Eurydice_array_to_slice((size_t)168U, buffers.data, uint8_t),
          Eurydice_array_to_slice((size_t)168U, &buffers.data[1U], uint8_t),
          Eurydice_array_to_slice((size_t)168U, &buffers.data[2U], uint8_t),
          Eurydice_array_to_slice((size_t)168U, &buffers.data[3U], uint8_t)}};
  load_block_3a(state, &lvalue, (size_t)0U);
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
static void load_last_8f_c6(Eurydice_arr_05 *self, Eurydice_arr_d9 *input,
                            size_t start, size_t len) {
  load_last_c6(self, input, start, len);
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
static KRML_MUSTINLINE void absorb_final_80_fb0(Eurydice_arr_05 *self,
                                                Eurydice_arr_d9 *last,
                                                size_t start, size_t len) {
  load_last_8f_c6(self, last, start, len);
  keccakf1600_80_a6(self);
}

/**
 Absorb
*/
void libcrux_sha3_avx2_x4_incremental_shake128_absorb_final(
    Eurydice_arr_05 *s, Eurydice_slice data0, Eurydice_slice data1,
    Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_arr_05 *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d9 lvalue = {.data = {data0, data1, data2, data3}};
  Eurydice_arr_d9 *uu____1 = &lvalue;
  absorb_final_80_fb0(uu____0, uu____1, (size_t)0U,
                      Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.avx2.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void store_block_3a(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3, size_t start, size_t len) {
  size_t chunks = len / (size_t)32U;
  for (size_t i = (size_t)0U; i < chunks; i++) {
    size_t i4 = i;
    size_t i0 = (size_t)4U * i4 / (size_t)5U;
    size_t j0 = (size_t)4U * i4 % (size_t)5U;
    size_t i1 = ((size_t)4U * i4 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)4U * i4 + (size_t)1U) % (size_t)5U;
    size_t i2 = ((size_t)4U * i4 + (size_t)2U) / (size_t)5U;
    size_t j2 = ((size_t)4U * i4 + (size_t)2U) % (size_t)5U;
    size_t i3 = ((size_t)4U * i4 + (size_t)3U) / (size_t)5U;
    size_t j3 = ((size_t)4U * i4 + (size_t)3U) % (size_t)5U;
    __m256i v0l =
        mm256_permute2x128_si256((int32_t)32, get_ij_a6(s, i0, j0)[0U],
                                 get_ij_a6(s, i2, j2)[0U], __m256i);
    __m256i v1h =
        mm256_permute2x128_si256((int32_t)32, get_ij_a6(s, i1, j1)[0U],
                                 get_ij_a6(s, i3, j3)[0U], __m256i);
    __m256i v2l =
        mm256_permute2x128_si256((int32_t)49, get_ij_a6(s, i0, j0)[0U],
                                 get_ij_a6(s, i2, j2)[0U], __m256i);
    __m256i v3h =
        mm256_permute2x128_si256((int32_t)49, get_ij_a6(s, i1, j1)[0U],
                                 get_ij_a6(s, i3, j3)[0U], __m256i);
    __m256i v0 = mm256_unpacklo_epi64(v0l, v1h);
    __m256i v1 = mm256_unpackhi_epi64(v0l, v1h);
    __m256i v2 = mm256_unpacklo_epi64(v2l, v3h);
    __m256i v3 = mm256_unpackhi_epi64(v2l, v3h);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out0, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v0);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out1, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v1);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out2, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v2);
    mm256_storeu_si256_u8(
        Eurydice_slice_subslice3(out3, start + (size_t)32U * i4,
                                 start + (size_t)32U * (i4 + (size_t)1U),
                                 uint8_t *),
        v3);
    continue;
  }
  size_t rem = len % (size_t)32U;
  if (rem > (size_t)0U) {
    size_t start0 = start + (size_t)32U * chunks;
    Eurydice_arr_60 u8s = {.data = {0U}};
    size_t chunks8 = rem / (size_t)8U;
    for (size_t i0 = (size_t)0U; i0 < chunks8; i0++) {
      size_t k = i0;
      size_t i = ((size_t)4U * chunks + k) / (size_t)5U;
      size_t j = ((size_t)4U * chunks + k) % (size_t)5U;
      mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, &u8s, uint8_t),
                            get_ij_a6(s, i, j)[0U]);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out0, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)0U, (size_t)8U, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out1, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)8U, (size_t)16U, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out2, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)16U, (size_t)24U,
                                      uint8_t *),
          uint8_t);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out3, start0 + (size_t)8U * k,
                                   start0 + (size_t)8U * (k + (size_t)1U),
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)24U, (size_t)32U,
                                      uint8_t *),
          uint8_t);
    }
    size_t rem8 = rem % (size_t)8U;
    if (rem8 > (size_t)0U) {
      size_t i = ((size_t)4U * chunks + chunks8) / (size_t)5U;
      size_t j = ((size_t)4U * chunks + chunks8) % (size_t)5U;
      mm256_storeu_si256_u8(Eurydice_array_to_slice((size_t)32U, &u8s, uint8_t),
                            get_ij_a6(s, i, j)[0U]);
      Eurydice_slice_copy(
          Eurydice_slice_subslice3(out0, start0 + len - rem8, start0 + len,
                                   uint8_t *),
          Eurydice_array_to_subslice3(&u8s, (size_t)0U, rem, uint8_t *),
          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out1, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)8U, (size_t)8U + rem, uint8_t *),
                          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out2, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)16U, (size_t)16U + rem, uint8_t *),
                          uint8_t);
      Eurydice_slice_copy(Eurydice_slice_subslice3(out3, start0 + len - rem8,
                                                   start0 + len, uint8_t *),
                          Eurydice_array_to_subslice3(
                              &u8s, (size_t)24U, (size_t)24U + rem, uint8_t *),
                          uint8_t);
    }
  }
  return;
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
A monomorphic instance of libcrux_sha3.simd.avx2.squeeze_17
with const generics
- RATE= 168
*/
static void squeeze_17_3a(Eurydice_arr_05 *self, Eurydice_slice out0,
                          Eurydice_slice out1, Eurydice_slice out2,
                          Eurydice_slice out3, size_t start, size_t len) {
  store_block_3a(self, out0, out1, out2, out3, start, len);
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
static KRML_MUSTINLINE void squeeze_first_three_blocks_81_3a(
    Eurydice_arr_05 *self, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)0U, (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)168U, (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)2U * (size_t)168U,
                (size_t)168U);
}

/**
 Squeeze three blocks
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_three_blocks(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_first_three_blocks_81_3a(s, out0, out1, out2, out3);
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
static KRML_MUSTINLINE void squeeze_next_block_81_3a(
    Eurydice_arr_05 *self, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3, size_t start) {
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, start, (size_t)168U);
}

/**
 Squeeze another block
*/
void libcrux_sha3_avx2_x4_incremental_shake128_squeeze_next_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_next_block_81_3a(s, out0, out1, out2, out3, (size_t)0U);
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
libcrux_sha3.generic_keccak.simd256.squeeze_first_five_blocks_81 with const
generics
- RATE= 168
*/
static KRML_MUSTINLINE void squeeze_first_five_blocks_81_3a(
    Eurydice_arr_05 *self, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)0U, (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)168U, (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)2U * (size_t)168U,
                (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)3U * (size_t)168U,
                (size_t)168U);
  keccakf1600_80_a6(self);
  squeeze_17_3a(self, out0, out1, out2, out3, (size_t)4U * (size_t)168U,
                (size_t)168U);
}

/**
 Squeeze five blocks
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake128_squeeze_first_five_blocks(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_first_five_blocks_81_3a(s, out0, out1, out2, out3);
}

/**
 Absorb
*/
KRML_MUSTINLINE void libcrux_sha3_avx2_x4_incremental_shake256_absorb_final(
    Eurydice_arr_05 *s, Eurydice_slice data0, Eurydice_slice data1,
    Eurydice_slice data2, Eurydice_slice data3) {
  Eurydice_arr_05 *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d9 lvalue = {.data = {data0, data1, data2, data3}};
  Eurydice_arr_d9 *uu____1 = &lvalue;
  absorb_final_80_fb(uu____0, uu____1, (size_t)0U,
                     Eurydice_slice_len(data0, uint8_t));
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
libcrux_sha3.generic_keccak.simd256.squeeze_first_block_81 with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_first_block_81_5b(Eurydice_arr_05 *self,
                                                      Eurydice_slice out0,
                                                      Eurydice_slice out1,
                                                      Eurydice_slice out2,
                                                      Eurydice_slice out3) {
  squeeze_17_5b(self, out0, out1, out2, out3, (size_t)0U, (size_t)136U);
}

/**
 Squeeze block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_first_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_first_block_81_5b(s, out0, out1, out2, out3);
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
- RATE= 136
*/
static KRML_MUSTINLINE void squeeze_next_block_81_5b(
    Eurydice_arr_05 *self, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3, size_t start) {
  keccakf1600_80_a6(self);
  squeeze_17_5b(self, out0, out1, out2, out3, start, (size_t)136U);
}

/**
 Squeeze next block
*/
KRML_MUSTINLINE void
libcrux_sha3_avx2_x4_incremental_shake256_squeeze_next_block(
    Eurydice_arr_05 *s, Eurydice_slice out0, Eurydice_slice out1,
    Eurydice_slice out2, Eurydice_slice out3) {
  squeeze_next_block_81_5b(s, out0, out1, out2, out3, (size_t)0U);
}
