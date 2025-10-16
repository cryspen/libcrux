/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: ec7dfaf71369de6c7ab306a7ada725b6fc004a33
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 23ba8451a39d29970cc274e93bb0b2fe91fbc040
 */


#include "internal/libcrux_sha3_neon.h"

#include "libcrux_sha3_portable.h"
#include "libcrux_core.h"
#include "internal/libcrux_core.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t zero_f7(void)
{
  return _vdupq_n_u64(0ULL);
}

static KRML_MUSTINLINE uint64x2_t
_veor5q_u64(uint64x2_t a, uint64x2_t b, uint64x2_t c, uint64x2_t d, uint64x2_t e)
{
  return _veor3q_u64(_veor3q_u64(a, b, c), d, e);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t
xor5_f7(uint64x2_t a, uint64x2_t b, uint64x2_t c, uint64x2_t d, uint64x2_t e)
{
  return _veor5q_u64(a, b, c, d, e);
}

static KRML_MUSTINLINE uint64x2_t _vrax1q_u640(uint64x2_t a, uint64x2_t b)
{
  return _vrax1q_u64(a, b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t rotate_left1_and_xor_f7(uint64x2_t a, uint64x2_t b)
{
  return _vrax1q_u640(a, b);
}

static KRML_MUSTINLINE uint64x2_t _vbcaxq_u640(uint64x2_t a, uint64x2_t b, uint64x2_t c)
{
  return _vbcaxq_u64(a, b, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t and_not_xor_f7(uint64x2_t a, uint64x2_t b, uint64x2_t c)
{
  return _vbcaxq_u640(a, b, c);
}

static KRML_MUSTINLINE uint64x2_t _veorq_n_u64(uint64x2_t a, uint64_t c)
{
  uint64x2_t c0 = _vdupq_n_u64(c);
  return _veorq_u64(a, c0);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t xor_constant_f7(uint64x2_t a, uint64_t c)
{
  return _veorq_n_u64(a, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
static KRML_MUSTINLINE uint64x2_t xor_f7(uint64x2_t a, uint64x2_t b)
{
  return _veorq_u64(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE Eurydice_arr_fe new_80_65(void)
{
  Eurydice_arr_fe lit;
  uint64x2_t repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++)
  {
    repeat_expression[i] = zero_f7();
  }
  memcpy(lit.data, repeat_expression, (size_t)25U * sizeof (uint64x2_t));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE uint64x2_t *get_ij_65(Eurydice_arr_fe *arr, size_t i, size_t j)
{
  return &arr->data[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void
set_ij_65(Eurydice_arr_fe *arr, size_t i, size_t j, uint64x2_t value)
{
  arr->data[(size_t)5U * j + i] = value;
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void
load_block_f8(Eurydice_arr_fe *s, Eurydice_arr_7d *blocks, size_t offset)
{
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t start = offset + (size_t)16U * i2;
    uint64x2_t
    v0 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[0U],
          start,
          start + (size_t)16U,
          uint8_t *));
    uint64x2_t
    v1 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[1U],
          start,
          start + (size_t)16U,
          uint8_t *));
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    set_ij_65(s, i0, j0, _veorq_u64(get_ij_65(s, i0, j0)[0U], _vtrn1q_u64(v0, v1)));
    set_ij_65(s, i1, j1, _veorq_u64(get_ij_65(s, i1, j1)[0U], _vtrn2q_u64(v0, v1)));
  }
  if ((size_t)72U % (size_t)16U != (size_t)0U)
  {
    size_t i = (size_t)72U / (size_t)8U - (size_t)1U;
    Eurydice_arr_e1 u = { .data = { 0U } };
    size_t start = offset + (size_t)72U - (size_t)8U;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    u.data[0U] = core_num__u64__from_le_bytes(uu____0);
    core_result_Result_a4 dst0;
    Eurydice_slice_to_array2(&dst0,
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____1 = core_result_unwrap_26_ab(dst0);
    u.data[1U] = core_num__u64__from_le_bytes(uu____1);
    uint64x2_t uvec = _vld1q_u64(Eurydice_array_to_slice((size_t)2U, &u, uint64_t));
    set_ij_65(s,
      i / (size_t)5U,
      i % (size_t)5U,
      _veorq_u64(get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U], uvec));
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_3e
with const generics
- RATE= 72
*/
static void load_block_3e_f8(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start)
{
  load_block_f8(self, input, start);
}

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static uint64x2_t *index_c2_65(Eurydice_arr_fe *self, size_t_x2 index)
{
  return get_ij_65(self, index.fst, index.snd);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.set_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static void set_80_65(Eurydice_arr_fe *self, size_t i, size_t j, uint64x2_t v)
{
  set_ij_65(self, i, j, v);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_02(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)36, (int32_t)28, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 36
- RIGHT= 28
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_02(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_ac(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)3, (int32_t)61, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 3
- RIGHT= 61
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_ac(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_020(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)41, (int32_t)23, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 41
- RIGHT= 23
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_020(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_a9(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)18, (int32_t)46, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 18
- RIGHT= 46
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_a9(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_76(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)1, (int32_t)63, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 1
- RIGHT= 63
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_76(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_58(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)44, (int32_t)20, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 44
- RIGHT= 20
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_58(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_e0(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)10, (int32_t)54, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 10
- RIGHT= 54
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_e0(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_63(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)45, (int32_t)19, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 45
- RIGHT= 19
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_63(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_6a(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)2, (int32_t)62, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 2
- RIGHT= 62
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_6a(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_ab(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)62, (int32_t)2, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 62
- RIGHT= 2
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_ab(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_5b(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)6, (int32_t)58, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 6
- RIGHT= 58
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_5b(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_6f(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)43, (int32_t)21, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 43
- RIGHT= 21
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_6f(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_62(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)15, (int32_t)49, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 15
- RIGHT= 49
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_62(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_23(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)61, (int32_t)3, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 61
- RIGHT= 3
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_23(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_37(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)28, (int32_t)36, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 28
- RIGHT= 36
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_37(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_bb(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)55, (int32_t)9, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 55
- RIGHT= 9
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_bb(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_b9(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)25, (int32_t)39, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 25
- RIGHT= 39
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_b9(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_54(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)21, (int32_t)43, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 21
- RIGHT= 43
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_54(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_4c(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)56, (int32_t)8, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 56
- RIGHT= 8
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_4c(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_ce(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)27, (int32_t)37, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 27
- RIGHT= 37
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_ce(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_77(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)20, (int32_t)44, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 20
- RIGHT= 44
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_77(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_25(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)39, (int32_t)25, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 39
- RIGHT= 25
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_25(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_af(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)8, (int32_t)56, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 8
- RIGHT= 56
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_af(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64x2_t _vxarq_u64_fd(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64((int32_t)14, (int32_t)50, a, b, uint64x2_t);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.xor_and_rotate_f7
with const generics
- LEFT= 14
- RIGHT= 50
*/
static KRML_MUSTINLINE uint64x2_t xor_and_rotate_f7_fd(uint64x2_t a, uint64x2_t b)
{
  return _vxarq_u64_fd(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void theta_rho_80_65(Eurydice_arr_fe *self)
{
  Eurydice_arr_4d
  c =
    {
      .data = {
        xor5_f7(index_c2_65(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U]),
        xor5_f7(index_c2_65(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U]),
        xor5_f7(index_c2_65(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U]),
        xor5_f7(index_c2_65(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U]),
        xor5_f7(index_c2_65(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U],
          index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U])
      }
    };
  Eurydice_arr_4d
  t =
    {
      .data = {
        rotate_left1_and_xor_f7(c.data[((size_t)0U + (size_t)4U) % (size_t)5U],
          c.data[((size_t)0U + (size_t)1U) % (size_t)5U]),
        rotate_left1_and_xor_f7(c.data[((size_t)1U + (size_t)4U) % (size_t)5U],
          c.data[((size_t)1U + (size_t)1U) % (size_t)5U]),
        rotate_left1_and_xor_f7(c.data[((size_t)2U + (size_t)4U) % (size_t)5U],
          c.data[((size_t)2U + (size_t)1U) % (size_t)5U]),
        rotate_left1_and_xor_f7(c.data[((size_t)3U + (size_t)4U) % (size_t)5U],
          c.data[((size_t)3U + (size_t)1U) % (size_t)5U]),
        rotate_left1_and_xor_f7(c.data[((size_t)4U + (size_t)4U) % (size_t)5U],
          c.data[((size_t)4U + (size_t)1U) % (size_t)5U])
      }
    };
  set_80_65(self,
    (size_t)0U,
    (size_t)0U,
    xor_f7(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  set_80_65(self,
    (size_t)1U,
    (size_t)0U,
    xor_and_rotate_f7_02(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  set_80_65(self,
    (size_t)2U,
    (size_t)0U,
    xor_and_rotate_f7_ac(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  set_80_65(self,
    (size_t)3U,
    (size_t)0U,
    xor_and_rotate_f7_020(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  set_80_65(self,
    (size_t)4U,
    (size_t)0U,
    xor_and_rotate_f7_a9(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  set_80_65(self,
    (size_t)0U,
    (size_t)1U,
    xor_and_rotate_f7_76(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  set_80_65(self,
    (size_t)1U,
    (size_t)1U,
    xor_and_rotate_f7_58(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  set_80_65(self,
    (size_t)2U,
    (size_t)1U,
    xor_and_rotate_f7_e0(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  set_80_65(self,
    (size_t)3U,
    (size_t)1U,
    xor_and_rotate_f7_63(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  set_80_65(self,
    (size_t)4U,
    (size_t)1U,
    xor_and_rotate_f7_6a(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  set_80_65(self,
    (size_t)0U,
    (size_t)2U,
    xor_and_rotate_f7_ab(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  set_80_65(self,
    (size_t)1U,
    (size_t)2U,
    xor_and_rotate_f7_5b(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  set_80_65(self,
    (size_t)2U,
    (size_t)2U,
    xor_and_rotate_f7_6f(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  set_80_65(self,
    (size_t)3U,
    (size_t)2U,
    xor_and_rotate_f7_62(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  set_80_65(self,
    (size_t)4U,
    (size_t)2U,
    xor_and_rotate_f7_23(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  set_80_65(self,
    (size_t)0U,
    (size_t)3U,
    xor_and_rotate_f7_37(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  set_80_65(self,
    (size_t)1U,
    (size_t)3U,
    xor_and_rotate_f7_bb(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  set_80_65(self,
    (size_t)2U,
    (size_t)3U,
    xor_and_rotate_f7_b9(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  set_80_65(self,
    (size_t)3U,
    (size_t)3U,
    xor_and_rotate_f7_54(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  set_80_65(self,
    (size_t)4U,
    (size_t)3U,
    xor_and_rotate_f7_4c(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  set_80_65(self,
    (size_t)0U,
    (size_t)4U,
    xor_and_rotate_f7_ce(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  set_80_65(self,
    (size_t)1U,
    (size_t)4U,
    xor_and_rotate_f7_77(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  set_80_65(self,
    (size_t)2U,
    (size_t)4U,
    xor_and_rotate_f7_25(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  set_80_65(self,
    (size_t)3U,
    (size_t)4U,
    xor_and_rotate_f7_af(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  set_80_65(self,
    (size_t)4U,
    (size_t)4U,
    xor_and_rotate_f7_fd(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void pi_80_65(Eurydice_arr_fe *self)
{
  Eurydice_arr_fe old = self[0U];
  set_80_65(self,
    (size_t)1U,
    (size_t)0U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U]);
  set_80_65(self,
    (size_t)2U,
    (size_t)0U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U]);
  set_80_65(self,
    (size_t)3U,
    (size_t)0U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U]);
  set_80_65(self,
    (size_t)4U,
    (size_t)0U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U]);
  set_80_65(self,
    (size_t)0U,
    (size_t)1U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U]);
  set_80_65(self,
    (size_t)1U,
    (size_t)1U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U]);
  set_80_65(self,
    (size_t)2U,
    (size_t)1U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U]);
  set_80_65(self,
    (size_t)3U,
    (size_t)1U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U]);
  set_80_65(self,
    (size_t)4U,
    (size_t)1U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U]);
  set_80_65(self,
    (size_t)0U,
    (size_t)2U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U]);
  set_80_65(self,
    (size_t)1U,
    (size_t)2U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U]);
  set_80_65(self,
    (size_t)2U,
    (size_t)2U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U]);
  set_80_65(self,
    (size_t)3U,
    (size_t)2U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U]);
  set_80_65(self,
    (size_t)4U,
    (size_t)2U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U]);
  set_80_65(self,
    (size_t)0U,
    (size_t)3U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U]);
  set_80_65(self,
    (size_t)1U,
    (size_t)3U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U]);
  set_80_65(self,
    (size_t)2U,
    (size_t)3U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U]);
  set_80_65(self,
    (size_t)3U,
    (size_t)3U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U]);
  set_80_65(self,
    (size_t)4U,
    (size_t)3U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U]);
  set_80_65(self,
    (size_t)0U,
    (size_t)4U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U]);
  set_80_65(self,
    (size_t)1U,
    (size_t)4U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U]);
  set_80_65(self,
    (size_t)2U,
    (size_t)4U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U]);
  set_80_65(self,
    (size_t)3U,
    (size_t)4U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U]);
  set_80_65(self,
    (size_t)4U,
    (size_t)4U,
    index_c2_65(&old, (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U]);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void chi_80_65(Eurydice_arr_fe *self)
{
  Eurydice_arr_fe old = self[0U];
  KRML_MAYBE_FOR5(i0,
    (size_t)0U,
    (size_t)5U,
    (size_t)1U,
    size_t i1 = i0;
    KRML_MAYBE_FOR5(i,
      (size_t)0U,
      (size_t)5U,
      (size_t)1U,
      size_t j = i;
      set_80_65(self,
        i1,
        j,
        and_not_xor_f7(index_c2_65(self, (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = j }))[0U],
          index_c2_65(&old,
            (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = (j + (size_t)2U) % (size_t)5U }))[0U],
          index_c2_65(&old,
            (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = (j + (size_t)1U) % (size_t)5U }))[0U]));););
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void iota_80_65(Eurydice_arr_fe *self, size_t i)
{
  set_80_65(self,
    (size_t)0U,
    (size_t)0U,
    xor_constant_f7(index_c2_65(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
      LIBCRUX_SHA3_GENERIC_KECCAK_CONSTANTS_ROUNDCONSTANTS.data[i]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
*/
static KRML_MUSTINLINE void keccakf1600_80_65(Eurydice_arr_fe *self)
{
  for (size_t i = (size_t)0U; i < (size_t)24U; i++)
  {
    size_t i0 = i;
    theta_rho_80_65(self);
    pi_80_65(self);
    chi_80_65(self);
    iota_80_65(self, i0);
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
*/
static KRML_MUSTINLINE void
absorb_block_80_20(Eurydice_arr_fe *self, Eurydice_arr_7d *blocks, size_t start)
{
  load_block_3e_f8(self, blocks, start);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 72
- DELIMITER= 6
*/
static KRML_MUSTINLINE void
load_last_96(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_a0 buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 6U;
  size_t uu____0 = (size_t)72U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_a0 buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 6U;
  size_t uu____1 = (size_t)72U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)72U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)72U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_f8(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 72
- DELIMITER= 6
*/
static void
load_last_3e_96(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_96(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 72
- DELIM= 6
*/
static KRML_MUSTINLINE void
absorb_final_80_76(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_96(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 72
*/
static KRML_MUSTINLINE void
store_block_f8(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  for (size_t i = (size_t)0U; i < len / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out0,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out1,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v1);
  }
  size_t remaining = len % (size_t)16U;
  if (remaining > (size_t)8U)
  {
    Eurydice_arr_88 out0_tmp = { .data = { 0U } };
    Eurydice_arr_88 out1_tmp = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    size_t i0 = i / (size_t)5U;
    size_t j0 = i % (size_t)5U;
    size_t i1 = (i + (size_t)1U) / (size_t)5U;
    size_t j1 = (i + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out0_tmp, uint8_t), v0);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out1_tmp, uint8_t), v1);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out0_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out1_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
  else if (remaining > (size_t)0U)
  {
    Eurydice_arr_88 out01 = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out01, uint8_t),
      get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U]);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)8U, (size_t)8U + remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.squeeze_d3
with const generics
- RATE= 72
*/
static void
squeeze_d3_f8(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  store_block_f8(self, out0, out1, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.keccak2
with const generics
- RATE= 72
- DELIM= 6
*/
static inline void keccak2_96(Eurydice_arr_7d *data, Eurydice_slice out0, Eurydice_slice out1)
{
  Eurydice_arr_fe s = new_80_65();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)72U; i++)
  {
    size_t i0 = i;
    absorb_block_80_20(&s, data, i0 * (size_t)72U);
  }
  size_t rem = data_len % (size_t)72U;
  absorb_final_80_76(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U)
  {
    squeeze_d3_f8(&s, out0, out1, (size_t)0U, outlen);
  }
  else
  {
    squeeze_d3_f8(&s, out0, out1, (size_t)0U, (size_t)72U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      keccakf1600_80_65(&s);
      squeeze_d3_f8(&s, out0, out1, i0 * (size_t)72U, (size_t)72U);
    }
    if (last < outlen)
    {
      keccakf1600_80_65(&s);
      squeeze_d3_f8(&s, out0, out1, last, outlen - last);
    }
  }
}

/**
 A SHA3 512 implementation.
*/
void libcrux_sha3_neon_sha512(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_Sha3_512Digest dummy = { .data = { 0U } };
  Eurydice_arr_7d uu____0 = { .data = { data, data } };
  keccak2_96(&uu____0, digest, Eurydice_array_to_slice((size_t)64U, &dummy, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void
load_block_5b(Eurydice_arr_fe *s, Eurydice_arr_7d *blocks, size_t offset)
{
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t start = offset + (size_t)16U * i2;
    uint64x2_t
    v0 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[0U],
          start,
          start + (size_t)16U,
          uint8_t *));
    uint64x2_t
    v1 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[1U],
          start,
          start + (size_t)16U,
          uint8_t *));
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    set_ij_65(s, i0, j0, _veorq_u64(get_ij_65(s, i0, j0)[0U], _vtrn1q_u64(v0, v1)));
    set_ij_65(s, i1, j1, _veorq_u64(get_ij_65(s, i1, j1)[0U], _vtrn2q_u64(v0, v1)));
  }
  if ((size_t)136U % (size_t)16U != (size_t)0U)
  {
    size_t i = (size_t)136U / (size_t)8U - (size_t)1U;
    Eurydice_arr_e1 u = { .data = { 0U } };
    size_t start = offset + (size_t)136U - (size_t)8U;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    u.data[0U] = core_num__u64__from_le_bytes(uu____0);
    core_result_Result_a4 dst0;
    Eurydice_slice_to_array2(&dst0,
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____1 = core_result_unwrap_26_ab(dst0);
    u.data[1U] = core_num__u64__from_le_bytes(uu____1);
    uint64x2_t uvec = _vld1q_u64(Eurydice_array_to_slice((size_t)2U, &u, uint64_t));
    set_ij_65(s,
      i / (size_t)5U,
      i % (size_t)5U,
      _veorq_u64(get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U], uvec));
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_3e
with const generics
- RATE= 136
*/
static void load_block_3e_5b(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start)
{
  load_block_5b(self, input, start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
*/
static KRML_MUSTINLINE void
absorb_block_80_200(Eurydice_arr_fe *self, Eurydice_arr_7d *blocks, size_t start)
{
  load_block_3e_5b(self, blocks, start);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 136
- DELIMITER= 6
*/
static KRML_MUSTINLINE void
load_last_ad(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_3d buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 6U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_3d buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 6U;
  size_t uu____1 = (size_t)136U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)136U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)136U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_5b(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 136
- DELIMITER= 6
*/
static void
load_last_3e_ad(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_ad(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 6
*/
static KRML_MUSTINLINE void
absorb_final_80_760(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_ad(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void
store_block_5b(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  for (size_t i = (size_t)0U; i < len / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out0,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out1,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v1);
  }
  size_t remaining = len % (size_t)16U;
  if (remaining > (size_t)8U)
  {
    Eurydice_arr_88 out0_tmp = { .data = { 0U } };
    Eurydice_arr_88 out1_tmp = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    size_t i0 = i / (size_t)5U;
    size_t j0 = i % (size_t)5U;
    size_t i1 = (i + (size_t)1U) / (size_t)5U;
    size_t j1 = (i + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out0_tmp, uint8_t), v0);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out1_tmp, uint8_t), v1);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out0_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out1_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
  else if (remaining > (size_t)0U)
  {
    Eurydice_arr_88 out01 = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out01, uint8_t),
      get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U]);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)8U, (size_t)8U + remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.squeeze_d3
with const generics
- RATE= 136
*/
static void
squeeze_d3_5b(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  store_block_5b(self, out0, out1, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.keccak2
with const generics
- RATE= 136
- DELIM= 6
*/
static inline void keccak2_ad(Eurydice_arr_7d *data, Eurydice_slice out0, Eurydice_slice out1)
{
  Eurydice_arr_fe s = new_80_65();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++)
  {
    size_t i0 = i;
    absorb_block_80_200(&s, data, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  absorb_final_80_760(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U)
  {
    squeeze_d3_5b(&s, out0, out1, (size_t)0U, outlen);
  }
  else
  {
    squeeze_d3_5b(&s, out0, out1, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      keccakf1600_80_65(&s);
      squeeze_d3_5b(&s, out0, out1, i0 * (size_t)136U, (size_t)136U);
    }
    if (last < outlen)
    {
      keccakf1600_80_65(&s);
      squeeze_d3_5b(&s, out0, out1, last, outlen - last);
    }
  }
}

/**
 A SHA3 256 implementation.
*/
void libcrux_sha3_neon_sha256(Eurydice_slice digest, Eurydice_slice data)
{
  Eurydice_arr_60 dummy = { .data = { 0U } };
  Eurydice_arr_7d uu____0 = { .data = { data, data } };
  keccak2_ad(&uu____0, digest, Eurydice_array_to_slice((size_t)32U, &dummy, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
static KRML_MUSTINLINE void
load_last_ad0(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_3d buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 31U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_3d buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 31U;
  size_t uu____1 = (size_t)136U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)136U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)136U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_5b(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 136
- DELIMITER= 31
*/
static void
load_last_3e_ad0(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_ad0(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 136
- DELIM= 31
*/
static KRML_MUSTINLINE void
absorb_final_80_761(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_ad0(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.keccak2
with const generics
- RATE= 136
- DELIM= 31
*/
static inline void keccak2_ad0(Eurydice_arr_7d *data, Eurydice_slice out0, Eurydice_slice out1)
{
  Eurydice_arr_fe s = new_80_65();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++)
  {
    size_t i0 = i;
    absorb_block_80_200(&s, data, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  absorb_final_80_761(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U)
  {
    squeeze_d3_5b(&s, out0, out1, (size_t)0U, outlen);
  }
  else
  {
    squeeze_d3_5b(&s, out0, out1, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      keccakf1600_80_65(&s);
      squeeze_d3_5b(&s, out0, out1, i0 * (size_t)136U, (size_t)136U);
    }
    if (last < outlen)
    {
      keccakf1600_80_65(&s);
      squeeze_d3_5b(&s, out0, out1, last, outlen - last);
    }
  }
}

/**
 Run SHAKE256 on both inputs in parallel.

 Writes the two results into `out0` and `out1`
*/
void
libcrux_sha3_neon_x2_shake256(
  Eurydice_slice input0,
  Eurydice_slice input1,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d lvalue = { .data = { input0, input1 } };
  keccak2_ad0(&lvalue, out0, out1);
}

/**
 Initialise the `KeccakState2`.
*/
Eurydice_arr_fe libcrux_sha3_neon_x2_incremental_init(void)
{
  return new_80_65();
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
load_block_3a(Eurydice_arr_fe *s, Eurydice_arr_7d *blocks, size_t offset)
{
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t start = offset + (size_t)16U * i2;
    uint64x2_t
    v0 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[0U],
          start,
          start + (size_t)16U,
          uint8_t *));
    uint64x2_t
    v1 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[1U],
          start,
          start + (size_t)16U,
          uint8_t *));
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    set_ij_65(s, i0, j0, _veorq_u64(get_ij_65(s, i0, j0)[0U], _vtrn1q_u64(v0, v1)));
    set_ij_65(s, i1, j1, _veorq_u64(get_ij_65(s, i1, j1)[0U], _vtrn2q_u64(v0, v1)));
  }
  if ((size_t)168U % (size_t)16U != (size_t)0U)
  {
    size_t i = (size_t)168U / (size_t)8U - (size_t)1U;
    Eurydice_arr_e1 u = { .data = { 0U } };
    size_t start = offset + (size_t)168U - (size_t)8U;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    u.data[0U] = core_num__u64__from_le_bytes(uu____0);
    core_result_Result_a4 dst0;
    Eurydice_slice_to_array2(&dst0,
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____1 = core_result_unwrap_26_ab(dst0);
    u.data[1U] = core_num__u64__from_le_bytes(uu____1);
    uint64x2_t uvec = _vld1q_u64(Eurydice_array_to_slice((size_t)2U, &u, uint64_t));
    set_ij_65(s,
      i / (size_t)5U,
      i % (size_t)5U,
      _veorq_u64(get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U], uvec));
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
static KRML_MUSTINLINE void
load_last_c6(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_27 buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 31U;
  size_t uu____0 = (size_t)168U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_27 buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 31U;
  size_t uu____1 = (size_t)168U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)168U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)168U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_3a(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 168
- DELIMITER= 31
*/
static void
load_last_3e_c6(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_c6(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 168
- DELIM= 31
*/
static KRML_MUSTINLINE void
absorb_final_80_762(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_c6(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
 Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_absorb_final(
  Eurydice_arr_fe *s,
  Eurydice_slice data0,
  Eurydice_slice data1
)
{
  Eurydice_arr_fe *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d lvalue = { .data = { data0, data1 } };
  Eurydice_arr_7d *uu____1 = &lvalue;
  absorb_final_80_762(uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
store_block_3a(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  for (size_t i = (size_t)0U; i < len / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out0,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out1,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v1);
  }
  size_t remaining = len % (size_t)16U;
  if (remaining > (size_t)8U)
  {
    Eurydice_arr_88 out0_tmp = { .data = { 0U } };
    Eurydice_arr_88 out1_tmp = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    size_t i0 = i / (size_t)5U;
    size_t j0 = i % (size_t)5U;
    size_t i1 = (i + (size_t)1U) / (size_t)5U;
    size_t j1 = (i + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out0_tmp, uint8_t), v0);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out1_tmp, uint8_t), v1);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out0_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out1_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
  else if (remaining > (size_t)0U)
  {
    Eurydice_arr_88 out01 = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out01, uint8_t),
      get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U]);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)8U, (size_t)8U + remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.squeeze_d3
with const generics
- RATE= 168
*/
static void
squeeze_d3_3a(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  store_block_3a(self, out0, out1, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.squeeze_first_three_blocks_7a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
squeeze_first_three_blocks_7a_3a(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_d3_3a(self, out0, out1, (size_t)0U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)168U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)2U * (size_t)168U, (size_t)168U);
}

/**
 Squeeze 2 times the first three blocks in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_three_blocks(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_first_three_blocks_7a_3a(s, out0, out1);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.squeeze_next_block_7a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
squeeze_next_block_7a_3a(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start
)
{
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, start, (size_t)168U);
}

/**
 Squeeze 2 times the next block in parallel in the
 [`KeccakState`] and return the output in `out0` and `out1`.
*/
void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_next_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_next_block_7a_3a(s, out0, out1, (size_t)0U);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void
load_block_2c(Eurydice_arr_fe *s, Eurydice_arr_7d *blocks, size_t offset)
{
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t start = offset + (size_t)16U * i2;
    uint64x2_t
    v0 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[0U],
          start,
          start + (size_t)16U,
          uint8_t *));
    uint64x2_t
    v1 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[1U],
          start,
          start + (size_t)16U,
          uint8_t *));
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    set_ij_65(s, i0, j0, _veorq_u64(get_ij_65(s, i0, j0)[0U], _vtrn1q_u64(v0, v1)));
    set_ij_65(s, i1, j1, _veorq_u64(get_ij_65(s, i1, j1)[0U], _vtrn2q_u64(v0, v1)));
  }
  if ((size_t)144U % (size_t)16U != (size_t)0U)
  {
    size_t i = (size_t)144U / (size_t)8U - (size_t)1U;
    Eurydice_arr_e1 u = { .data = { 0U } };
    size_t start = offset + (size_t)144U - (size_t)8U;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    u.data[0U] = core_num__u64__from_le_bytes(uu____0);
    core_result_Result_a4 dst0;
    Eurydice_slice_to_array2(&dst0,
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____1 = core_result_unwrap_26_ab(dst0);
    u.data[1U] = core_num__u64__from_le_bytes(uu____1);
    uint64x2_t uvec = _vld1q_u64(Eurydice_array_to_slice((size_t)2U, &u, uint64_t));
    set_ij_65(s,
      i / (size_t)5U,
      i % (size_t)5U,
      _veorq_u64(get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U], uvec));
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_3e
with const generics
- RATE= 144
*/
static void load_block_3e_2c(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start)
{
  load_block_2c(self, input, start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
*/
static KRML_MUSTINLINE void
absorb_block_80_201(Eurydice_arr_fe *self, Eurydice_arr_7d *blocks, size_t start)
{
  load_block_3e_2c(self, blocks, start);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 144
- DELIMITER= 6
*/
static KRML_MUSTINLINE void
load_last_1e(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_a8 buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 6U;
  size_t uu____0 = (size_t)144U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_a8 buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 6U;
  size_t uu____1 = (size_t)144U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)144U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)144U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_2c(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 144
- DELIMITER= 6
*/
static void
load_last_3e_1e(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_1e(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 144
- DELIM= 6
*/
static KRML_MUSTINLINE void
absorb_final_80_763(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_1e(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 144
*/
static KRML_MUSTINLINE void
store_block_2c(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  for (size_t i = (size_t)0U; i < len / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out0,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out1,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v1);
  }
  size_t remaining = len % (size_t)16U;
  if (remaining > (size_t)8U)
  {
    Eurydice_arr_88 out0_tmp = { .data = { 0U } };
    Eurydice_arr_88 out1_tmp = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    size_t i0 = i / (size_t)5U;
    size_t j0 = i % (size_t)5U;
    size_t i1 = (i + (size_t)1U) / (size_t)5U;
    size_t j1 = (i + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out0_tmp, uint8_t), v0);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out1_tmp, uint8_t), v1);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out0_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out1_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
  else if (remaining > (size_t)0U)
  {
    Eurydice_arr_88 out01 = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out01, uint8_t),
      get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U]);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)8U, (size_t)8U + remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.squeeze_d3
with const generics
- RATE= 144
*/
static void
squeeze_d3_2c(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  store_block_2c(self, out0, out1, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.keccak2
with const generics
- RATE= 144
- DELIM= 6
*/
static inline void keccak2_1e(Eurydice_arr_7d *data, Eurydice_slice out0, Eurydice_slice out1)
{
  Eurydice_arr_fe s = new_80_65();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)144U; i++)
  {
    size_t i0 = i;
    absorb_block_80_201(&s, data, i0 * (size_t)144U);
  }
  size_t rem = data_len % (size_t)144U;
  absorb_final_80_763(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U)
  {
    squeeze_d3_2c(&s, out0, out1, (size_t)0U, outlen);
  }
  else
  {
    squeeze_d3_2c(&s, out0, out1, (size_t)0U, (size_t)144U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      keccakf1600_80_65(&s);
      squeeze_d3_2c(&s, out0, out1, i0 * (size_t)144U, (size_t)144U);
    }
    if (last < outlen)
    {
      keccakf1600_80_65(&s);
      squeeze_d3_2c(&s, out0, out1, last, outlen - last);
    }
  }
}

/**
 A SHA3 224 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_neon_sha224(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_Sha3_224Digest dummy = { .data = { 0U } };
  Eurydice_arr_7d uu____0 = { .data = { data, data } };
  keccak2_1e(&uu____0, digest, Eurydice_array_to_slice((size_t)28U, &dummy, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void
load_block_7a(Eurydice_arr_fe *s, Eurydice_arr_7d *blocks, size_t offset)
{
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t start = offset + (size_t)16U * i2;
    uint64x2_t
    v0 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[0U],
          start,
          start + (size_t)16U,
          uint8_t *));
    uint64x2_t
    v1 =
      _vld1q_bytes_u64(Eurydice_slice_subslice3(blocks->data[1U],
          start,
          start + (size_t)16U,
          uint8_t *));
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    set_ij_65(s, i0, j0, _veorq_u64(get_ij_65(s, i0, j0)[0U], _vtrn1q_u64(v0, v1)));
    set_ij_65(s, i1, j1, _veorq_u64(get_ij_65(s, i1, j1)[0U], _vtrn2q_u64(v0, v1)));
  }
  if ((size_t)104U % (size_t)16U != (size_t)0U)
  {
    size_t i = (size_t)104U / (size_t)8U - (size_t)1U;
    Eurydice_arr_e1 u = { .data = { 0U } };
    size_t start = offset + (size_t)104U - (size_t)8U;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks->data[0U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    u.data[0U] = core_num__u64__from_le_bytes(uu____0);
    core_result_Result_a4 dst0;
    Eurydice_slice_to_array2(&dst0,
      Eurydice_slice_subslice3(blocks->data[1U], start, start + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____1 = core_result_unwrap_26_ab(dst0);
    u.data[1U] = core_num__u64__from_le_bytes(uu____1);
    uint64x2_t uvec = _vld1q_u64(Eurydice_array_to_slice((size_t)2U, &u, uint64_t));
    set_ij_65(s,
      i / (size_t)5U,
      i % (size_t)5U,
      _veorq_u64(get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U], uvec));
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_block_3e
with const generics
- RATE= 104
*/
static void load_block_3e_7a(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start)
{
  load_block_7a(self, input, start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
*/
static KRML_MUSTINLINE void
absorb_block_80_202(Eurydice_arr_fe *self, Eurydice_arr_7d *blocks, size_t start)
{
  load_block_3e_7a(self, blocks, start);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last
with const generics
- RATE= 104
- DELIMITER= 6
*/
static KRML_MUSTINLINE void
load_last_7c(Eurydice_arr_fe *state, Eurydice_arr_7d *blocks, size_t offset, size_t len)
{
  Eurydice_arr_18 buffer0 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer0, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[0U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer0.data[len] = 6U;
  size_t uu____0 = (size_t)104U - (size_t)1U;
  buffer0.data[uu____0] = (uint32_t)buffer0.data[uu____0] | 128U;
  Eurydice_arr_18 buffer1 = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer1, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks->data[1U], offset, offset + len, uint8_t *),
    uint8_t);
  buffer1.data[len] = 6U;
  size_t uu____1 = (size_t)104U - (size_t)1U;
  buffer1.data[uu____1] = (uint32_t)buffer1.data[uu____1] | 128U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d
  lvalue =
    {
      .data = {
        Eurydice_array_to_slice((size_t)104U,
          &buffer0,
          uint8_t),
        Eurydice_array_to_slice((size_t)104U,
          &buffer1,
          uint8_t)
      }
    };
  load_block_7a(state, &lvalue, (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<2usize> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.load_last_3e
with const generics
- RATE= 104
- DELIMITER= 6
*/
static void
load_last_3e_7c(Eurydice_arr_fe *self, Eurydice_arr_7d *input, size_t start, size_t len)
{
  load_last_7c(self, input, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- N= 2
- RATE= 104
- DELIM= 6
*/
static KRML_MUSTINLINE void
absorb_final_80_764(Eurydice_arr_fe *self, Eurydice_arr_7d *last, size_t start, size_t len)
{
  load_last_3e_7c(self, last, start, len);
  keccakf1600_80_65(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.arm64.store_block
with const generics
- RATE= 104
*/
static KRML_MUSTINLINE void
store_block_7a(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  for (size_t i = (size_t)0U; i < len / (size_t)16U; i++)
  {
    size_t i2 = i;
    size_t i0 = (size_t)2U * i2 / (size_t)5U;
    size_t j0 = (size_t)2U * i2 % (size_t)5U;
    size_t i1 = ((size_t)2U * i2 + (size_t)1U) / (size_t)5U;
    size_t j1 = ((size_t)2U * i2 + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out0,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v0);
    _vst1q_bytes_u64(Eurydice_slice_subslice3(out1,
        start + (size_t)16U * i2,
        start + (size_t)16U * (i2 + (size_t)1U),
        uint8_t *),
      v1);
  }
  size_t remaining = len % (size_t)16U;
  if (remaining > (size_t)8U)
  {
    Eurydice_arr_88 out0_tmp = { .data = { 0U } };
    Eurydice_arr_88 out1_tmp = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    size_t i0 = i / (size_t)5U;
    size_t j0 = i % (size_t)5U;
    size_t i1 = (i + (size_t)1U) / (size_t)5U;
    size_t j1 = (i + (size_t)1U) % (size_t)5U;
    uint64x2_t v0 = _vtrn1q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    uint64x2_t v1 = _vtrn2q_u64(get_ij_65(s, i0, j0)[0U], get_ij_65(s, i1, j1)[0U]);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out0_tmp, uint8_t), v0);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out1_tmp, uint8_t), v1);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out0_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out1_tmp, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
  else if (remaining > (size_t)0U)
  {
    Eurydice_arr_88 out01 = { .data = { 0U } };
    size_t i = (size_t)2U * (len / (size_t)16U);
    _vst1q_bytes_u64(Eurydice_array_to_slice((size_t)16U, &out01, uint8_t),
      get_ij_65(s, i / (size_t)5U, i % (size_t)5U)[0U]);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out0,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)0U, remaining, uint8_t *),
      uint8_t);
    Eurydice_slice_copy(Eurydice_slice_subslice3(out1,
        start + len - remaining,
        start + len,
        uint8_t *),
      Eurydice_array_to_subslice3(&out01, (size_t)8U, (size_t)8U + remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t> for libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.arm64.squeeze_d3
with const generics
- RATE= 104
*/
static void
squeeze_d3_7a(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start,
  size_t len
)
{
  store_block_7a(self, out0, out1, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.keccak2
with const generics
- RATE= 104
- DELIM= 6
*/
static inline void keccak2_7c(Eurydice_arr_7d *data, Eurydice_slice out0, Eurydice_slice out1)
{
  Eurydice_arr_fe s = new_80_65();
  size_t data_len = Eurydice_slice_len(data->data[0U], uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)104U; i++)
  {
    size_t i0 = i;
    absorb_block_80_202(&s, data, i0 * (size_t)104U);
  }
  size_t rem = data_len % (size_t)104U;
  absorb_final_80_764(&s, data, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out0, uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U)
  {
    squeeze_d3_7a(&s, out0, out1, (size_t)0U, outlen);
  }
  else
  {
    squeeze_d3_7a(&s, out0, out1, (size_t)0U, (size_t)104U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      keccakf1600_80_65(&s);
      squeeze_d3_7a(&s, out0, out1, i0 * (size_t)104U, (size_t)104U);
    }
    if (last < outlen)
    {
      keccakf1600_80_65(&s);
      squeeze_d3_7a(&s, out0, out1, last, outlen - last);
    }
  }
}

/**
 A SHA3 384 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_neon_sha384(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_Sha3_384Digest dummy = { .data = { 0U } };
  Eurydice_arr_7d uu____0 = { .data = { data, data } };
  keccak2_7c(&uu____0, digest, Eurydice_array_to_slice((size_t)48U, &dummy, uint8_t));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.squeeze_first_five_blocks_7a
with const generics
- RATE= 168
*/
static KRML_MUSTINLINE void
squeeze_first_five_blocks_7a_3a(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_d3_3a(self, out0, out1, (size_t)0U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)168U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)2U * (size_t)168U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)3U * (size_t)168U, (size_t)168U);
  keccakf1600_80_65(self);
  squeeze_d3_3a(self, out0, out1, (size_t)4U * (size_t)168U, (size_t)168U);
}

/**
 Squeeze five blocks
*/
KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake128_squeeze_first_five_blocks(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_first_five_blocks_7a_3a(s, out0, out1);
}

/**
 Shake256 absorb `data0` and `data1` in the [`KeccakState`] `s`.
*/
KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_absorb_final(
  Eurydice_arr_fe *s,
  Eurydice_slice data0,
  Eurydice_slice data1
)
{
  Eurydice_arr_fe *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_7d lvalue = { .data = { data0, data1 } };
  Eurydice_arr_7d *uu____1 = &lvalue;
  absorb_final_80_761(uu____0, uu____1, (size_t)0U, Eurydice_slice_len(data0, uint8_t));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.squeeze_first_block_7a
with const generics
- RATE= 136
*/
static void
squeeze_first_block_7a_5b(Eurydice_arr_fe *self, Eurydice_slice out0, Eurydice_slice out1)
{
  squeeze_d3_5b(self, out0, out1, (size_t)0U, (size_t)136U);
}

/**
 Squeeze block
*/
KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_first_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_first_block_7a_5b(s, out0, out1);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<core::core_arch::arm_shared::neon::uint64x2_t, 2usize>[core::marker::Sized<core::core_arch::arm_shared::neon::uint64x2_t>, libcrux_sha3::simd::arm64::{libcrux_sha3::traits::KeccakItem<2usize> for core::core_arch::arm_shared::neon::uint64x2_t}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.simd128.squeeze_next_block_7a
with const generics
- RATE= 136
*/
static KRML_MUSTINLINE void
squeeze_next_block_7a_5b(
  Eurydice_arr_fe *self,
  Eurydice_slice out0,
  Eurydice_slice out1,
  size_t start
)
{
  keccakf1600_80_65(self);
  squeeze_d3_5b(self, out0, out1, start, (size_t)136U);
}

/**
 Squeeze next block
*/
KRML_MUSTINLINE void
libcrux_sha3_neon_x2_incremental_shake256_squeeze_next_block(
  Eurydice_arr_fe *s,
  Eurydice_slice out0,
  Eurydice_slice out1
)
{
  squeeze_next_block_7a_5b(s, out0, out1, (size_t)0U);
}

