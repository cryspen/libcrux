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


#ifndef libcrux_sha3_portable_H
#define libcrux_sha3_portable_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_sha3_internal.h"
#include "libcrux_core.h"

#define LIBCRUX_SHA3_GENERIC_KECCAK_CONSTANTS_ROUNDCONSTANTS ((KRML_CLITERAL(Eurydice_arr_a7){ .data = { 1ULL, 32898ULL, 9223372036854808714ULL, 9223372039002292224ULL, 32907ULL, 2147483649ULL, 9223372039002292353ULL, 9223372036854808585ULL, 138ULL, 136ULL, 2147516425ULL, 2147483658ULL, 2147516555ULL, 9223372036854775947ULL, 9223372036854808713ULL, 9223372036854808579ULL, 9223372036854808578ULL, 9223372036854775936ULL, 32778ULL, 9223372039002259466ULL, 9223372039002292353ULL, 9223372036854808704ULL, 2147483649ULL, 9223372039002292232ULL } }))

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_zero_d2(void);

uint64_t
libcrux_sha3_simd_portable__veor5q_u64(
  uint64_t a,
  uint64_t b,
  uint64_t c,
  uint64_t d,
  uint64_t e
);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t
libcrux_sha3_simd_portable_xor5_d2(uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 1
- RIGHT= 63
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_76(uint64_t x);

uint64_t libcrux_sha3_simd_portable__vrax1q_u64(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(uint64_t a, uint64_t b);

uint64_t libcrux_sha3_simd_portable__vbcaxq_u64(uint64_t a, uint64_t b, uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_and_not_xor_d2(uint64_t a, uint64_t b, uint64_t c);

uint64_t libcrux_sha3_simd_portable__veorq_n_u64(uint64_t a, uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_xor_constant_d2(uint64_t a, uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_xor_d2(uint64_t a, uint64_t b);

typedef struct size_t_x2_s
{
  size_t fst;
  size_t snd;
}
size_t_x2;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types uint64_t
with const generics
- $1size_t
*/
typedef Eurydice_arr_26 libcrux_sha3_generic_keccak_KeccakState_17;

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types uint64_t
with const generics
- N= 1
*/
Eurydice_arr_26 libcrux_sha3_generic_keccak_new_80_04(void);

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types uint64_t
with const generics
- N= 1
*/
uint64_t *libcrux_sha3_traits_get_ij_04(Eurydice_arr_26 *arr, size_t i, size_t j);

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_traits_set_ij_04(Eurydice_arr_26 *arr, size_t i, size_t j, uint64_t value);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 72
*/
void
libcrux_sha3_simd_portable_load_block_f8(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
);

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
);

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types uint64_t
with const generics
- N= 1
*/
uint64_t *libcrux_sha3_generic_keccak_index_c2_04(Eurydice_arr_26 *self, size_t_x2 index);

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
libcrux_sha3_generic_keccak_set_80_04(Eurydice_arr_26 *self, size_t i, size_t j, uint64_t v);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 36
- RIGHT= 28
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_02(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 36
- RIGHT= 28
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_02(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 36
- RIGHT= 28
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_02(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 3
- RIGHT= 61
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_ac(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 3
- RIGHT= 61
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_ac(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 3
- RIGHT= 61
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 41
- RIGHT= 23
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_020(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 41
- RIGHT= 23
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_020(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 41
- RIGHT= 23
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_020(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 18
- RIGHT= 46
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_a9(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 18
- RIGHT= 46
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_a9(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 18
- RIGHT= 46
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 1
- RIGHT= 63
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_76(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 1
- RIGHT= 63
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_76(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 44
- RIGHT= 20
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_58(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 44
- RIGHT= 20
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_58(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 44
- RIGHT= 20
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_58(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 10
- RIGHT= 54
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_e0(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 10
- RIGHT= 54
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_e0(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 10
- RIGHT= 54
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 45
- RIGHT= 19
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_63(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 45
- RIGHT= 19
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_63(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 45
- RIGHT= 19
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_63(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 2
- RIGHT= 62
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_6a(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 2
- RIGHT= 62
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_6a(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 2
- RIGHT= 62
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 62
- RIGHT= 2
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_ab(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 62
- RIGHT= 2
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_ab(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 62
- RIGHT= 2
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 6
- RIGHT= 58
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_5b(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 6
- RIGHT= 58
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_5b(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 6
- RIGHT= 58
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 43
- RIGHT= 21
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_6f(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 43
- RIGHT= 21
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_6f(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 43
- RIGHT= 21
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 15
- RIGHT= 49
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_62(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 15
- RIGHT= 49
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_62(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 15
- RIGHT= 49
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_62(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 61
- RIGHT= 3
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_23(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 61
- RIGHT= 3
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_23(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 61
- RIGHT= 3
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_23(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 28
- RIGHT= 36
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_37(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 28
- RIGHT= 36
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_37(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 28
- RIGHT= 36
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_37(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 55
- RIGHT= 9
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_bb(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 55
- RIGHT= 9
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_bb(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 55
- RIGHT= 9
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 25
- RIGHT= 39
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_b9(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 25
- RIGHT= 39
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_b9(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 25
- RIGHT= 39
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 21
- RIGHT= 43
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_54(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 21
- RIGHT= 43
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_54(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 21
- RIGHT= 43
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_54(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 56
- RIGHT= 8
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_4c(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 56
- RIGHT= 8
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_4c(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 56
- RIGHT= 8
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 27
- RIGHT= 37
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_ce(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 27
- RIGHT= 37
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_ce(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 27
- RIGHT= 37
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 20
- RIGHT= 44
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_77(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 20
- RIGHT= 44
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_77(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 20
- RIGHT= 44
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_77(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 39
- RIGHT= 25
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_25(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 39
- RIGHT= 25
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_25(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 39
- RIGHT= 25
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_25(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 8
- RIGHT= 56
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_af(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 8
- RIGHT= 56
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_af(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 8
- RIGHT= 56
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_af(uint64_t a, uint64_t b);

/**
A monomorphic instance of libcrux_sha3.simd.portable.rotate_left
with const generics
- LEFT= 14
- RIGHT= 50
*/
uint64_t libcrux_sha3_simd_portable_rotate_left_fd(uint64_t x);

/**
A monomorphic instance of libcrux_sha3.simd.portable._vxarq_u64
with const generics
- LEFT= 14
- RIGHT= 50
*/
uint64_t libcrux_sha3_simd_portable__vxarq_u64_fd(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.xor_and_rotate_d2
with const generics
- LEFT= 14
- RIGHT= 50
*/
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(uint64_t a, uint64_t b);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_theta_rho_80_04(Eurydice_arr_26 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_pi_80_04(Eurydice_arr_26 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_chi_80_04(Eurydice_arr_26 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_iota_80_04(Eurydice_arr_26 *self, size_t i);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_keccakf1600_80_04(Eurydice_arr_26 *self);

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
void
libcrux_sha3_generic_keccak_absorb_block_80_c6(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 72
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_96(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 72
*/
void
libcrux_sha3_simd_portable_store_block_f8(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
);

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
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_96(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_portable_sha512(Eurydice_slice digest, Eurydice_slice data);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 136
*/
void
libcrux_sha3_simd_portable_load_block_5b(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_block_80_c60(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_ad(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e0(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 136
*/
void
libcrux_sha3_simd_portable_store_block_5b(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
);

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
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_ad(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHA3 256 implementation.
*/
void libcrux_sha3_portable_sha256(Eurydice_slice digest, Eurydice_slice data);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 31
*/
void
libcrux_sha3_simd_portable_load_last_ad0(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e1(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_portable_keccak1_ad0(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHAKE256 implementation.
*/
void libcrux_sha3_portable_shake256(Eurydice_slice digest, Eurydice_slice data);

typedef libcrux_sha3_generic_keccak_KeccakState_17 libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
Eurydice_arr_26 libcrux_sha3_portable_incremental_shake128_init(void);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 168
*/
void
libcrux_sha3_simd_portable_load_block_3a(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
void
libcrux_sha3_simd_portable_load_last_c6(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e2(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
 Absorb
*/
void
libcrux_sha3_portable_incremental_shake128_absorb_final(
  Eurydice_arr_26 *s,
  Eurydice_slice data0
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 168
*/
void
libcrux_sha3_simd_portable_store_block_3a(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
);

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
);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_three_blocks_b4
with const generics
- RATE= 168
*/
void
libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out
);

/**
 Squeeze three blocks
*/
void
libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4
with const generics
- RATE= 168
*/
void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start
);

/**
 Squeeze another block
*/
void
libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
);

/**
 Returns the output size of a digest.
*/
size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 144
*/
void
libcrux_sha3_simd_portable_load_block_2c(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_block_80_c61(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 144
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_1e(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e3(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 144
*/
void
libcrux_sha3_simd_portable_store_block_2c(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
);

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
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_1e(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHA3 224 implementation.
*/
void libcrux_sha3_portable_sha224(Eurydice_slice digest, Eurydice_slice data);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 104
*/
void
libcrux_sha3_simd_portable_load_block_7a(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_block_80_c62(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 104
- DELIMITER= 6
*/
void
libcrux_sha3_simd_portable_load_last_7c(
  Eurydice_arr_26 *state,
  Eurydice_slice blocks,
  size_t start,
  size_t len
);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_final_80_9e4(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *last,
  size_t start,
  size_t len
);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 104
*/
void
libcrux_sha3_simd_portable_store_block_7a(
  Eurydice_arr_26 *s,
  Eurydice_slice out,
  size_t start,
  size_t len
);

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
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_7c(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHA3 384 implementation.
*/
void libcrux_sha3_portable_sha384(Eurydice_slice digest, Eurydice_slice data);

/**
 SHA3 224

 Preconditions:
 - `digest.len() == 28`
*/
void libcrux_sha3_sha224_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 224
*/
libcrux_sha3_Sha3_224Digest libcrux_sha3_sha224(Eurydice_slice data);

/**
 SHA3 256
*/
void libcrux_sha3_sha256_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 256
*/
Eurydice_arr_60 libcrux_sha3_sha256(Eurydice_slice data);

/**
 SHA3 384
*/
void libcrux_sha3_sha384_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 384
*/
libcrux_sha3_Sha3_384Digest libcrux_sha3_sha384(Eurydice_slice data);

/**
 SHA3 512
*/
void libcrux_sha3_sha512_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 512
*/
libcrux_sha3_Sha3_512Digest libcrux_sha3_sha512(Eurydice_slice data);

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
);

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
void
libcrux_sha3_generic_keccak_absorb_block_80_c63(
  Eurydice_arr_26 *self,
  Eurydice_arr_34 *blocks,
  size_t start
);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_portable_keccak1_c6(Eurydice_slice data, Eurydice_slice out);

/**
 A portable SHAKE128 implementation.
*/
void libcrux_sha3_portable_shake128(Eurydice_slice digest, Eurydice_slice data);

/**
 SHAKE 128

 Writes `out.len()` bytes.
*/
void libcrux_sha3_shake128_ema(Eurydice_slice out, Eurydice_slice data);

/**
 SHAKE 256

 Writes `out.len()` bytes.
*/
void libcrux_sha3_shake256_ema(Eurydice_slice out, Eurydice_slice data);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_five_blocks_b4
with const generics
- RATE= 168
*/
void
libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(
  Eurydice_arr_26 *self,
  Eurydice_slice out
);

/**
 Squeeze five blocks
*/
void
libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
  Eurydice_arr_26 *s,
  Eurydice_slice out0
);

/**
 Absorb some data for SHAKE-256 for the last time
*/
void
libcrux_sha3_portable_incremental_shake256_absorb_final(
  Eurydice_arr_26 *s,
  Eurydice_slice data
);

/**
 Create a new SHAKE-256 state object.
*/
Eurydice_arr_26 libcrux_sha3_portable_incremental_shake256_init(void);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_first_block_b4
with const generics
- RATE= 136
*/
void
libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(
  Eurydice_arr_26 *self,
  Eurydice_slice out
);

/**
 Squeeze the first SHAKE-256 block
*/
void
libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out
);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>, libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4
with const generics
- RATE= 136
*/
void
libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(
  Eurydice_arr_26 *self,
  Eurydice_slice out,
  size_t start
);

/**
 Squeeze the next SHAKE-256 block
*/
void
libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
  Eurydice_arr_26 *s,
  Eurydice_slice out
);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_sha3_portable_KeccakState
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_73_s { Eurydice_arr_26 data[2U]; } Eurydice_arr_73;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_sha3_portable_KeccakState
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_180_s { Eurydice_arr_26 data[4U]; } Eurydice_arr_180;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_sha3_portable_KeccakState
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_e4_s { Eurydice_arr_26 data[3U]; } Eurydice_arr_e4;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- $2size_t
*/
typedef Eurydice_arr_fe libcrux_sha3_generic_keccak_KeccakState_bb;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_e2_s
{
  Eurydice_arr_26 inner;
  Eurydice_arr_c40 buf;
  size_t buf_len;
  bool sponge;
}
libcrux_sha3_generic_keccak_xof_KeccakXofState_e2;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
libcrux_sha3_portable_incremental_Shake256Xof;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_97_s
{
  Eurydice_arr_26 inner;
  Eurydice_arr_75 buf;
  size_t buf_len;
  bool sponge;
}
libcrux_sha3_generic_keccak_xof_KeccakXofState_97;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_97
libcrux_sha3_portable_incremental_Shake128Xof;

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_portable_H_DEFINED
#endif /* libcrux_sha3_portable_H */
