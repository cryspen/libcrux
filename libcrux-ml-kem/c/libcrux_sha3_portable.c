/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9b87e8727803cd306b94c18b0ceb0b5b1c18c0e9
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */


#include "libcrux_sha3_portable.h"

#include "libcrux_sha3_internal.h"
#include "libcrux_core.h"
#include "internal/libcrux_core.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_zero_d2(void)
{
  return 0ULL;
}

KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__veor5q_u64(
  uint64_t a,
  uint64_t b,
  uint64_t c,
  uint64_t d,
  uint64_t e
)
{
  return (((a ^ b) ^ c) ^ d) ^ e;
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor5_d2(uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e)
{
  return libcrux_sha3_simd_portable__veor5q_u64(a, b, c, d, e);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_76(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)1);
}

KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vrax1q_u64(uint64_t a, uint64_t b)
{
  uint64_t uu____0 = a;
  return uu____0 ^ libcrux_sha3_simd_portable_rotate_left_76(b);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vrax1q_u64(a, b);
}

KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable__vbcaxq_u64(uint64_t a, uint64_t b, uint64_t c)
{
  return a ^ (b & ~c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_and_not_xor_d2(uint64_t a, uint64_t b, uint64_t c)
{
  return libcrux_sha3_simd_portable__vbcaxq_u64(a, b, c);
}

KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__veorq_n_u64(uint64_t a, uint64_t c)
{
  return a ^ c;
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_xor_constant_d2(uint64_t a, uint64_t c)
{
  return libcrux_sha3_simd_portable__veorq_n_u64(a, c);
}

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_xor_d2(uint64_t a, uint64_t b)
{
  return a ^ b;
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE Eurydice_arr_26 libcrux_sha3_generic_keccak_new_80_04(void)
{
  Eurydice_arr_26 lit;
  uint64_t repeat_expression[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++)
  {
    repeat_expression[i] = libcrux_sha3_simd_portable_zero_d2();
  }
  memcpy(lit.data, repeat_expression, (size_t)25U * sizeof (uint64_t));
  return lit;
}

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE uint64_t
*libcrux_sha3_traits_get_ij_04(Eurydice_arr_26 *arr, size_t i, size_t j)
{
  return &arr->data[(size_t)5U * j + i];
}

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void
libcrux_sha3_traits_set_ij_04(Eurydice_arr_26 *arr, size_t i, size_t j, uint64_t value)
{
  arr->data[(size_t)5U * j + i] = value;
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_block_f8(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
)
{
  Eurydice_arr_26 state_flat = { .data = { 0U } };
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++)
  {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    state_flat.data[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(state,
      i0 / (size_t)5U,
      i0 % (size_t)5U,
      libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U, i0 % (size_t)5U)[0U] ^
        state_flat.data[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 72
*/
void
libcrux_sha3_simd_portable_load_block_a1_f8(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_f8(self, input->data[0U], start);
}

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types uint64_t
with const generics
- N= 1
*/
uint64_t *libcrux_sha3_generic_keccak_index_c2_04(Eurydice_arr_26 *self, size_t_x2 index)
{
  return libcrux_sha3_traits_get_ij_04(self, index.fst, index.snd);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.set_80
with types uint64_t
with const generics
- N= 1
*/
void
libcrux_sha3_generic_keccak_set_80_04(Eurydice_arr_26 *self, size_t i, size_t j, uint64_t v)
{
  libcrux_sha3_traits_set_ij_04(self, i, j, v);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_02(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)36);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_02(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_02(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_02(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_ac(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)3);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_ac(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_ac(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_020(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)41);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_020(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_020(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_020(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_a9(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)18);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_a9(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_a9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_76(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_76(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_76(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_58(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)44);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_58(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_58(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_58(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_e0(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)10);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_e0(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_e0(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_63(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)45);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_63(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_63(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_63(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_6a(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)2);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_6a(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_6a(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_ab(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)62);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_ab(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_ab(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_5b(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)6);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_5b(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_5b(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_6f(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)43);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_6f(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_6f(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_62(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)15);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_62(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_62(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_62(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_23(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)61);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_23(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_23(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_23(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_37(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)28);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_37(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_37(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_37(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_bb(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)55);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_bb(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_bb(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_b9(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)25);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_b9(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_b9(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_54(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)21);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_54(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_54(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_54(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_4c(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)56);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_4c(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_4c(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_ce(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)27);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_ce(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_ce(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_77(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)20);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_77(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_77(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_77(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_25(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)39);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_25(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_25(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_25(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_af(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)8);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_af(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_af(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_af(a, b);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable_rotate_left_fd(uint64_t x)
{
  return core_num__u64__rotate_left(x, (uint32_t)(int32_t)14);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
KRML_MUSTINLINE uint64_t libcrux_sha3_simd_portable__vxarq_u64_fd(uint64_t a, uint64_t b)
{
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
KRML_MUSTINLINE uint64_t
libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(uint64_t a, uint64_t b)
{
  return libcrux_sha3_simd_portable__vxarq_u64_fd(a, b);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void libcrux_sha3_generic_keccak_theta_rho_80_04(Eurydice_arr_26 *self)
{
  Eurydice_arr_a5
  c =
    {
      .data = {
        libcrux_sha3_simd_portable_xor5_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U]),
        libcrux_sha3_simd_portable_xor5_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U]),
        libcrux_sha3_simd_portable_xor5_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U]),
        libcrux_sha3_simd_portable_xor5_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U]),
        libcrux_sha3_simd_portable_xor5_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U])
      }
    };
  uint64_t
  uu____0 =
    libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(c.data[((size_t)0U + (size_t)4U) %
        (size_t)5U],
      c.data[((size_t)0U + (size_t)1U) % (size_t)5U]);
  uint64_t
  uu____1 =
    libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(c.data[((size_t)1U + (size_t)4U) %
        (size_t)5U],
      c.data[((size_t)1U + (size_t)1U) % (size_t)5U]);
  uint64_t
  uu____2 =
    libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(c.data[((size_t)2U + (size_t)4U) %
        (size_t)5U],
      c.data[((size_t)2U + (size_t)1U) % (size_t)5U]);
  uint64_t
  uu____3 =
    libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(c.data[((size_t)3U + (size_t)4U) %
        (size_t)5U],
      c.data[((size_t)3U + (size_t)1U) % (size_t)5U]);
  Eurydice_arr_a5
  t =
    {
      .data = {
        uu____0, uu____1, uu____2, uu____3,
        libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(c.data[((size_t)4U + (size_t)4U) %
            (size_t)5U],
          c.data[((size_t)4U + (size_t)1U) % (size_t)5U])
      }
    };
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  Eurydice_arr_26 *uu____4 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____4,
    (size_t)1U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_02(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  Eurydice_arr_26 *uu____5 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____5,
    (size_t)2U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  Eurydice_arr_26 *uu____6 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____6,
    (size_t)3U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_020(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  Eurydice_arr_26 *uu____7 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____7,
    (size_t)4U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U],
      t.data[0U]));
  Eurydice_arr_26 *uu____8 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____8,
    (size_t)0U,
    (size_t)1U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_76(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  Eurydice_arr_26 *uu____9 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____9,
    (size_t)1U,
    (size_t)1U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_58(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  Eurydice_arr_26 *uu____10 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____10,
    (size_t)2U,
    (size_t)1U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  Eurydice_arr_26 *uu____11 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____11,
    (size_t)3U,
    (size_t)1U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_63(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  Eurydice_arr_26 *uu____12 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____12,
    (size_t)4U,
    (size_t)1U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U],
      t.data[1U]));
  Eurydice_arr_26 *uu____13 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____13,
    (size_t)0U,
    (size_t)2U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  Eurydice_arr_26 *uu____14 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____14,
    (size_t)1U,
    (size_t)2U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  Eurydice_arr_26 *uu____15 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____15,
    (size_t)2U,
    (size_t)2U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  Eurydice_arr_26 *uu____16 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____16,
    (size_t)3U,
    (size_t)2U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_62(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  Eurydice_arr_26 *uu____17 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____17,
    (size_t)4U,
    (size_t)2U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_23(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U],
      t.data[2U]));
  Eurydice_arr_26 *uu____18 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____18,
    (size_t)0U,
    (size_t)3U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_37(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  Eurydice_arr_26 *uu____19 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____19,
    (size_t)1U,
    (size_t)3U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  Eurydice_arr_26 *uu____20 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____20,
    (size_t)2U,
    (size_t)3U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  Eurydice_arr_26 *uu____21 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____21,
    (size_t)3U,
    (size_t)3U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_54(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  Eurydice_arr_26 *uu____22 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____22,
    (size_t)4U,
    (size_t)3U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U],
      t.data[3U]));
  Eurydice_arr_26 *uu____23 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____23,
    (size_t)0U,
    (size_t)4U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  Eurydice_arr_26 *uu____24 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____24,
    (size_t)1U,
    (size_t)4U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_77(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  Eurydice_arr_26 *uu____25 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____25,
    (size_t)2U,
    (size_t)4U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_25(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  Eurydice_arr_26 *uu____26 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____26,
    (size_t)3U,
    (size_t)4U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_af(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
  Eurydice_arr_26 *uu____27 = self;
  libcrux_sha3_generic_keccak_set_80_04(uu____27,
    (size_t)4U,
    (size_t)4U,
    libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U],
      t.data[4U]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void libcrux_sha3_generic_keccak_pi_80_04(Eurydice_arr_26 *self)
{
  Eurydice_arr_26 old = self[0U];
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)1U,
    (size_t)0U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)3U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)2U,
    (size_t)0U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)1U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)3U,
    (size_t)0U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)4U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)4U,
    (size_t)0U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)2U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)1U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)1U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)1U,
    (size_t)1U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)4U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)2U,
    (size_t)1U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)2U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)3U,
    (size_t)1U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)0U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)4U,
    (size_t)1U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)1U, .snd = (size_t)3U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)2U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)2U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)1U,
    (size_t)2U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)0U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)2U,
    (size_t)2U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)3U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)3U,
    (size_t)2U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)1U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)4U,
    (size_t)2U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)2U, .snd = (size_t)4U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)3U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)3U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)1U,
    (size_t)3U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)1U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)2U,
    (size_t)3U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)4U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)3U,
    (size_t)3U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)2U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)4U,
    (size_t)3U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)3U, .snd = (size_t)0U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)4U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)4U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)1U,
    (size_t)4U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)2U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)2U,
    (size_t)4U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)0U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)3U,
    (size_t)4U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)3U }))[0U]);
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)4U,
    (size_t)4U,
    libcrux_sha3_generic_keccak_index_c2_04(&old,
      (KRML_CLITERAL(size_t_x2){ .fst = (size_t)4U, .snd = (size_t)1U }))[0U]);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void libcrux_sha3_generic_keccak_chi_80_04(Eurydice_arr_26 *self)
{
  Eurydice_arr_26 old = self[0U];
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
      libcrux_sha3_generic_keccak_set_80_04(self,
        i1,
        j,
        libcrux_sha3_simd_portable_and_not_xor_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
            (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = j }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(&old,
            (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = (j + (size_t)2U) % (size_t)5U }))[0U],
          libcrux_sha3_generic_keccak_index_c2_04(&old,
            (KRML_CLITERAL(size_t_x2){ .fst = i1, .snd = (j + (size_t)1U) % (size_t)5U }))[0U]));););
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void libcrux_sha3_generic_keccak_iota_80_04(Eurydice_arr_26 *self, size_t i)
{
  libcrux_sha3_generic_keccak_set_80_04(self,
    (size_t)0U,
    (size_t)0U,
    libcrux_sha3_simd_portable_xor_constant_d2(libcrux_sha3_generic_keccak_index_c2_04(self,
        (KRML_CLITERAL(size_t_x2){ .fst = (size_t)0U, .snd = (size_t)0U }))[0U],
      LIBCRUX_SHA3_GENERIC_KECCAK_CONSTANTS_ROUNDCONSTANTS.data[i]));
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types uint64_t
with const generics
- N= 1
*/
KRML_MUSTINLINE void libcrux_sha3_generic_keccak_keccakf1600_80_04(Eurydice_arr_26 *self)
{
  for (size_t i = (size_t)0U; i < (size_t)24U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_generic_keccak_theta_rho_80_04(self);
    libcrux_sha3_generic_keccak_pi_80_04(self);
    libcrux_sha3_generic_keccak_chi_80_04(self);
    libcrux_sha3_generic_keccak_iota_80_04(self, i0);
  }
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_block_80_c6(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_a1_f8(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 72
- DELIMITER= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_96(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_a0 buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 6U;
  size_t uu____0 = (size_t)72U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_f8(state,
    Eurydice_array_to_slice((size_t)72U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 72
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_a1_96(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_96(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_96(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_store_block_f8(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++)
  {
    size_t i0 = i;
    Eurydice_slice
    uu____0 =
      Eurydice_slice_subslice3(out,
        start + (size_t)8U * i0,
        start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          i0 / (size_t)5U,
          i0 % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice((size_t)8U, &lvalue, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U)
  {
    Eurydice_slice
    uu____1 = Eurydice_slice_subslice3(out, start + len - remaining, start + len, uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          octets / (size_t)5U,
          octets % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____1,
      Eurydice_array_to_subslice3(&lvalue, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 72
*/
void
libcrux_sha3_simd_portable_squeeze_13_f8(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_store_block_f8(self, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 72
- DELIM= 6
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_96(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)72U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c6(&s, &lvalue, i0 * (size_t)72U);
  }
  size_t rem = data_len % (size_t)72U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, (size_t)0U, (size_t)72U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, i0 * (size_t)72U, (size_t)72U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_f8(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_portable_sha512(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_96(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_block_5b(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
)
{
  Eurydice_arr_26 state_flat = { .data = { 0U } };
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++)
  {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    state_flat.data[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(state,
      i0 / (size_t)5U,
      i0 % (size_t)5U,
      libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U, i0 % (size_t)5U)[0U] ^
        state_flat.data[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 136
*/
void
libcrux_sha3_simd_portable_load_block_a1_5b(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_5b(self, input->data[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_block_80_c60(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_a1_5b(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_ad(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_3d buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 6U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_5b(state,
    Eurydice_array_to_slice((size_t)136U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_a1_ad(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_ad(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e0(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_ad(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_store_block_5b(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++)
  {
    size_t i0 = i;
    Eurydice_slice
    uu____0 =
      Eurydice_slice_subslice3(out,
        start + (size_t)8U * i0,
        start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          i0 / (size_t)5U,
          i0 % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice((size_t)8U, &lvalue, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U)
  {
    Eurydice_slice
    uu____1 = Eurydice_slice_subslice3(out, start + len - remaining, start + len, uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          octets / (size_t)5U,
          octets % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____1,
      Eurydice_array_to_subslice3(&lvalue, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 136
*/
void
libcrux_sha3_simd_portable_squeeze_13_5b(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_store_block_5b(self, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 6
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_ad(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c60(&s, &lvalue, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e0(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, i0 * (size_t)136U, (size_t)136U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 256 implementation.
*/
void libcrux_sha3_portable_sha256(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_ad(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_ad0(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_3d buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 31U;
  size_t uu____0 = (size_t)136U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_5b(state,
    Eurydice_array_to_slice((size_t)136U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 31
*/
void
libcrux_sha3_simd_portable_load_last_a1_ad0(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_ad0(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e1(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_ad0(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 31
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_ad0(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)136U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c60(&s, &lvalue, i0 * (size_t)136U);
  }
  size_t rem = data_len % (size_t)136U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e1(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, (size_t)0U, (size_t)136U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, i0 * (size_t)136U, (size_t)136U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_5b(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHAKE256 implementation.
*/
void libcrux_sha3_portable_shake256(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_ad0(data, digest);
}

/**
 Create a new SHAKE-128 state object.
*/
Eurydice_arr_26 libcrux_sha3_portable_incremental_shake128_init(void)
{
  return libcrux_sha3_generic_keccak_new_80_04();
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_block_3a(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
)
{
  Eurydice_arr_26 state_flat = { .data = { 0U } };
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++)
  {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    state_flat.data[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(state,
      i0 / (size_t)5U,
      i0 % (size_t)5U,
      libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U, i0 % (size_t)5U)[0U] ^
        state_flat.data[i0]);
  }
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_c6(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_27 buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 31U;
  size_t uu____0 = (size_t)168U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_3a(state,
    Eurydice_array_to_slice((size_t)168U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 168
- DELIMITER= 31
*/
void
libcrux_sha3_simd_portable_load_last_a1_c6(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_c6(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e2(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_c6(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
 Absorb
*/
void
libcrux_sha3_portable_incremental_shake128_absorb_final(
  Eurydice_arr_26 *s,
  Eurydice_slice data0
)
{
  Eurydice_arr_26 *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data0 } };
  Eurydice_arr_34 *uu____1 = &lvalue;
  libcrux_sha3_generic_keccak_absorb_final_80_9e2(uu____0,
    uu____1,
    (size_t)0U,
    Eurydice_slice_len(data0, uint8_t));
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_store_block_3a(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++)
  {
    size_t i0 = i;
    Eurydice_slice
    uu____0 =
      Eurydice_slice_subslice3(out,
        start + (size_t)8U * i0,
        start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          i0 / (size_t)5U,
          i0 % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice((size_t)8U, &lvalue, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U)
  {
    Eurydice_slice
    uu____1 = Eurydice_slice_subslice3(out, start + len - remaining, start + len, uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          octets / (size_t)5U,
          octets % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____1,
      Eurydice_array_to_subslice3(&lvalue, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 168
*/
void
libcrux_sha3_simd_portable_squeeze_13_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_store_block_3a(self, out, start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_three_blocks_b4
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out
)
{
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)0U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)168U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)2U * (size_t)168U, (size_t)168U);
}

/**
 Squeeze three blocks
*/
void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
)
{
  libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(s, out0);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start
)
{
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, start, (size_t)168U);
}

/**
 Squeeze another block
*/
void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
)
{
  libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(s, out0, (size_t)0U);
}

/**
 Returns the output size of a digest.
*/
size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode)
{
  switch (mode)
  {
    case libcrux_sha3_Algorithm_Sha224:
      {
        break;
      }
    case libcrux_sha3_Algorithm_Sha256:
      {
        return (size_t)32U;
      }
    case libcrux_sha3_Algorithm_Sha384:
      {
        return (size_t)48U;
      }
    case libcrux_sha3_Algorithm_Sha512:
      {
        return (size_t)64U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
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
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_block_2c(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
)
{
  Eurydice_arr_26 state_flat = { .data = { 0U } };
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++)
  {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    state_flat.data[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(state,
      i0 / (size_t)5U,
      i0 % (size_t)5U,
      libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U, i0 % (size_t)5U)[0U] ^
        state_flat.data[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 144
*/
void
libcrux_sha3_simd_portable_load_block_a1_2c(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_2c(self, input->data[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_block_80_c61(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_a1_2c(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 144
- DELIMITER= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_1e(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_a8 buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 6U;
  size_t uu____0 = (size_t)144U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_2c(state,
    Eurydice_array_to_slice((size_t)144U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 144
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_a1_1e(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_1e(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e3(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_1e(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_store_block_2c(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++)
  {
    size_t i0 = i;
    Eurydice_slice
    uu____0 =
      Eurydice_slice_subslice3(out,
        start + (size_t)8U * i0,
        start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          i0 / (size_t)5U,
          i0 % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice((size_t)8U, &lvalue, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U)
  {
    Eurydice_slice
    uu____1 = Eurydice_slice_subslice3(out, start + len - remaining, start + len, uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          octets / (size_t)5U,
          octets % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____1,
      Eurydice_array_to_subslice3(&lvalue, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 144
*/
void
libcrux_sha3_simd_portable_squeeze_13_2c(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_store_block_2c(self, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 144
- DELIM= 6
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_1e(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)144U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c61(&s, &lvalue, i0 * (size_t)144U);
  }
  size_t rem = data_len % (size_t)144U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e3(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, (size_t)0U, (size_t)144U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, i0 * (size_t)144U, (size_t)144U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_2c(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 224 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_portable_sha224(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_1e(data, digest);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_block_7a(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
)
{
  Eurydice_arr_26 state_flat = { .data = { 0U } };
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++)
  {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    core_result_Result_a4 dst;
    Eurydice_slice_to_array2(&dst,
      Eurydice_slice_subslice3(blocks, offset, offset + (size_t)8U, uint8_t *),
      Eurydice_slice,
      Eurydice_arr_c4,
      core_array_TryFromSliceError);
    Eurydice_arr_c4 uu____0 = core_result_unwrap_26_ab(dst);
    state_flat.data[i0] = core_num__u64__from_le_bytes(uu____0);
  }
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++)
  {
    size_t i0 = i;
    libcrux_sha3_traits_set_ij_04(state,
      i0 / (size_t)5U,
      i0 % (size_t)5U,
      libcrux_sha3_traits_get_ij_04(state, i0 / (size_t)5U, i0 % (size_t)5U)[0U] ^
        state_flat.data[i0]);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 104
*/
void
libcrux_sha3_simd_portable_load_block_a1_7a(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_7a(self, input->data[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_block_80_c62(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_a1_7a(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 104
- DELIMITER= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_load_last_7c(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
)
{
  Eurydice_arr_18 buffer = { .data = { 0U } };
  Eurydice_slice_copy(Eurydice_array_to_subslice3(&buffer, (size_t)0U, len, uint8_t *),
    Eurydice_slice_subslice3(blocks, start, start + len, uint8_t *),
    uint8_t);
  buffer.data[len] = 6U;
  size_t uu____0 = (size_t)104U - (size_t)1U;
  buffer.data[uu____0] = (uint32_t)buffer.data[uu____0] | 128U;
  libcrux_sha3_simd_portable_load_block_7a(state,
    Eurydice_array_to_slice((size_t)104U, &buffer, uint8_t),
    (size_t)0U);
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 104
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_a1_7c(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_7c(self, input->data[0U], start, len);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_final_80_9e4(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_load_last_a1_7c(self, last, start, len);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void
libcrux_sha3_simd_portable_store_block_7a(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  size_t octets = len / (size_t)8U;
  for (size_t i = (size_t)0U; i < octets; i++)
  {
    size_t i0 = i;
    Eurydice_slice
    uu____0 =
      Eurydice_slice_subslice3(out,
        start + (size_t)8U * i0,
        start + (size_t)8U * i0 + (size_t)8U,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          i0 / (size_t)5U,
          i0 % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice((size_t)8U, &lvalue, uint8_t), uint8_t);
  }
  size_t remaining = len % (size_t)8U;
  if (remaining > (size_t)0U)
  {
    Eurydice_slice
    uu____1 = Eurydice_slice_subslice3(out, start + len - remaining, start + len, uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_c4
    lvalue =
      core_num__u64__to_le_bytes(libcrux_sha3_traits_get_ij_04(s,
          octets / (size_t)5U,
          octets % (size_t)5U)[0U]);
    Eurydice_slice_copy(uu____1,
      Eurydice_array_to_subslice3(&lvalue, (size_t)0U, remaining, uint8_t *),
      uint8_t);
  }
}

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 104
*/
void
libcrux_sha3_simd_portable_squeeze_13_7a(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start,
  size_t len
)
{
  libcrux_sha3_simd_portable_store_block_7a(self, out, start, len);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 104
- DELIM= 6
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_7c(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)104U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c62(&s, &lvalue, i0 * (size_t)104U);
  }
  size_t rem = data_len % (size_t)104U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e4(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, (size_t)0U, (size_t)104U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, i0 * (size_t)104U, (size_t)104U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_7a(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHA3 384 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_portable_sha384(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_7c(data, digest);
}

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
KRML_MUSTINLINE void libcrux_sha3_sha224_ema(Eurydice_slice digest, Eurydice_slice payload)
{
  libcrux_sha3_portable_sha224(digest, payload);
}

/**
 SHA3 224
*/
KRML_MUSTINLINE libcrux_sha3_Sha3_224Digest libcrux_sha3_sha224(Eurydice_slice data)
{
  libcrux_sha3_Sha3_224Digest out = { .data = { 0U } };
  libcrux_sha3_sha224_ema(Eurydice_array_to_slice((size_t)28U, &out, uint8_t), data);
  return out;
}

/**
 SHA3 256
*/
KRML_MUSTINLINE void libcrux_sha3_sha256_ema(Eurydice_slice digest, Eurydice_slice payload)
{
  libcrux_sha3_portable_sha256(digest, payload);
}

/**
 SHA3 256
*/
KRML_MUSTINLINE Eurydice_arr_60 libcrux_sha3_sha256(Eurydice_slice data)
{
  Eurydice_arr_60 out = { .data = { 0U } };
  libcrux_sha3_sha256_ema(Eurydice_array_to_slice((size_t)32U, &out, uint8_t), data);
  return out;
}

/**
 SHA3 384
*/
KRML_MUSTINLINE void libcrux_sha3_sha384_ema(Eurydice_slice digest, Eurydice_slice payload)
{
  libcrux_sha3_portable_sha384(digest, payload);
}

/**
 SHA3 384
*/
KRML_MUSTINLINE libcrux_sha3_Sha3_384Digest libcrux_sha3_sha384(Eurydice_slice data)
{
  libcrux_sha3_Sha3_384Digest out = { .data = { 0U } };
  libcrux_sha3_sha384_ema(Eurydice_array_to_slice((size_t)48U, &out, uint8_t), data);
  return out;
}

/**
 SHA3 512
*/
KRML_MUSTINLINE void libcrux_sha3_sha512_ema(Eurydice_slice digest, Eurydice_slice payload)
{
  libcrux_sha3_portable_sha512(digest, payload);
}

/**
 SHA3 512
*/
KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest libcrux_sha3_sha512(Eurydice_slice data)
{
  libcrux_sha3_Sha3_512Digest out = { .data = { 0U } };
  libcrux_sha3_sha512_ema(Eurydice_array_to_slice((size_t)64U, &out, uint8_t), data);
  return out;
}

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 168
*/
void
libcrux_sha3_simd_portable_load_block_a1_3a(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *input,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_3a(self, input->data[0U], start);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_absorb_block_80_c63(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
)
{
  libcrux_sha3_simd_portable_load_block_a1_3a(self, blocks, start);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
}

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 168
- DELIM= 31
*/
inline void
libcrux_sha3_generic_keccak_portable_keccak1_c6(Eurydice_slice data, Eurydice_slice out)
{
  Eurydice_arr_26 s = libcrux_sha3_generic_keccak_new_80_04();
  size_t data_len = Eurydice_slice_len(data, uint8_t);
  for (size_t i = (size_t)0U; i < data_len / (size_t)168U; i++)
  {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_34 lvalue = { .data = { data } };
    libcrux_sha3_generic_keccak_absorb_block_80_c63(&s, &lvalue, i0 * (size_t)168U);
  }
  size_t rem = data_len % (size_t)168U;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  libcrux_sha3_generic_keccak_absorb_final_80_9e2(&s, &lvalue, data_len - rem, rem);
  size_t outlen = Eurydice_slice_len(out, uint8_t);
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  if (blocks == (size_t)0U)
  {
    libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, (size_t)0U, outlen);
  }
  else
  {
    libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, (size_t)0U, (size_t)168U);
    for (size_t i = (size_t)1U; i < blocks; i++)
    {
      size_t i0 = i;
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, i0 * (size_t)168U, (size_t)168U);
    }
    if (last < outlen)
    {
      libcrux_sha3_generic_keccak_keccakf1600_80_04(&s);
      libcrux_sha3_simd_portable_squeeze_13_3a(&s, out, last, outlen - last);
    }
  }
}

/**
 A portable SHAKE128 implementation.
*/
KRML_MUSTINLINE void libcrux_sha3_portable_shake128(Eurydice_slice digest, Eurydice_slice data)
{
  libcrux_sha3_generic_keccak_portable_keccak1_c6(data, digest);
}

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
KRML_MUSTINLINE void libcrux_sha3_shake128_ema(Eurydice_slice out, Eurydice_slice data)
{
  libcrux_sha3_portable_shake128(out, data);
}

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
KRML_MUSTINLINE void libcrux_sha3_shake256_ema(Eurydice_slice out, Eurydice_slice data)
{
  libcrux_sha3_portable_shake256(out, data);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_five_blocks_b4
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out
)
{
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)0U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)168U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)2U * (size_t)168U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)3U * (size_t)168U, (size_t)168U);
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_3a(self, out, (size_t)4U * (size_t)168U, (size_t)168U);
}

/**
 Squeeze five blocks
*/
KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
)
{
  libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(s, out0);
}

/**
 Absorb some data for SHAKE-256 for the last time
*/
KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_absorb_final(
  Eurydice_arr_26 *s,
  Eurydice_slice data
)
{
  Eurydice_arr_26 *uu____0 = s;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_34 lvalue = { .data = { data } };
  Eurydice_arr_34 *uu____1 = &lvalue;
  libcrux_sha3_generic_keccak_absorb_final_80_9e1(uu____0,
    uu____1,
    (size_t)0U,
    Eurydice_slice_len(data, uint8_t));
}

/**
 Create a new SHAKE-256 state object.
*/
KRML_MUSTINLINE Eurydice_arr_26 libcrux_sha3_portable_incremental_shake256_init(void)
{
  return libcrux_sha3_generic_keccak_new_80_04();
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_block_b4
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(
  Eurydice_arr_26 *self,
  Eurydice_slice out
)
{
  libcrux_sha3_simd_portable_squeeze_13_5b(self, out, (size_t)0U, (size_t)136U);
}

/**
 Squeeze the first SHAKE-256 block
*/
KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out
)
{
  libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(s, out);
}

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start
)
{
  libcrux_sha3_generic_keccak_keccakf1600_80_04(self);
  libcrux_sha3_simd_portable_squeeze_13_5b(self, out, start, (size_t)136U);
}

/**
 Squeeze the next SHAKE-256 block
*/
KRML_MUSTINLINE void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out
)
{
  libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(s, out, (size_t)0U);
}

