/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: unset
 * Libcrux: bf73a8a7a0f119e66b105a3462265b4a2a3af63b
 */

#ifndef libcrux_sha3_portable_H
#define libcrux_sha3_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_sha3_internal.h"

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_zero_d2(void);

uint64_t libcrux_sha3_simd_portable__veor5q_u64(uint64_t a, uint64_t b,
                                                uint64_t c, uint64_t d,
                                                uint64_t e);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_xor5_d2(uint64_t a, uint64_t b, uint64_t c,
                                            uint64_t d, uint64_t e);

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
uint64_t libcrux_sha3_simd_portable_rotate_left1_and_xor_d2(uint64_t a,
                                                            uint64_t b);

uint64_t libcrux_sha3_simd_portable__vbcaxq_u64(uint64_t a, uint64_t b,
                                                uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_and_not_xor_d2(uint64_t a, uint64_t b,
                                                   uint64_t c);

uint64_t libcrux_sha3_simd_portable__veorq_n_u64(uint64_t a, uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_xor_constant_d2(uint64_t a, uint64_t c);

/**
This function found in impl {libcrux_sha3::traits::KeccakItem<1usize> for u64}
*/
uint64_t libcrux_sha3_simd_portable_xor_d2(uint64_t a, uint64_t b);

extern const uint64_t libcrux_sha3_generic_keccak_constants_ROUNDCONSTANTS[24U];

typedef struct size_t_x2_s {
  size_t fst;
  size_t snd;
} size_t_x2;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.KeccakState
with types uint64_t
with const generics
- $1size_t
*/
typedef struct libcrux_sha3_generic_keccak_KeccakState_17_s {
  uint64_t st[25U];
} libcrux_sha3_generic_keccak_KeccakState_17;

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.new_80
with types uint64_t
with const generics
- N= 1
*/
libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_generic_keccak_new_80_04(void);

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types uint64_t
with const generics
- N= 1
*/
uint64_t *libcrux_sha3_traits_get_ij_04(uint64_t *arr, size_t i, size_t j);

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_traits_set_ij_04(uint64_t *arr, size_t i, size_t j,
                                   uint64_t value);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 72
*/
void libcrux_sha3_simd_portable_load_block_f8(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 72
*/
void libcrux_sha3_simd_portable_load_block_a1_f8(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start);

/**
This function found in impl {core::ops::index::Index<(usize, usize), T> for
libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.index_c2
with types uint64_t
with const generics
- N= 1
*/
uint64_t *libcrux_sha3_generic_keccak_index_c2_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t_x2 index);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_theta_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, uint64_t ret[5U]);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.set_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_set_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t i, size_t j,
    uint64_t v);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_02(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ac(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_020(uint64_t a,
                                                          uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_a9(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_76(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_58(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_e0(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_63(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_6a(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ab(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_5b(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_6f(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_62(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_23(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_37(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_bb(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_b9(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_54(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_4c(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_ce(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_77(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_25(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_af(uint64_t a,
                                                         uint64_t b);

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
uint64_t libcrux_sha3_simd_portable_xor_and_rotate_d2_fd(uint64_t a,
                                                         uint64_t b);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.rho_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_rho_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, uint64_t t[5U]);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_pi_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_chi_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_iota_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, size_t i);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600_80
with types uint64_t
with const generics
- N= 1
*/
void libcrux_sha3_generic_keccak_keccakf1600_80_04(
    libcrux_sha3_generic_keccak_KeccakState_17 *self);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
*/
void libcrux_sha3_generic_keccak_absorb_block_80_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 72
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_96(uint64_t *state,
                                             Eurydice_slice blocks,
                                             size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 72
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_a1_96(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 72
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 72
*/
void libcrux_sha3_simd_portable_store_block_f8(uint64_t *s, Eurydice_slice out,
                                               size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 72
*/
void libcrux_sha3_simd_portable_squeeze_13_f8(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_96(Eurydice_slice data,
                                                     Eurydice_slice out);

/**
 A portable SHA3 512 implementation.
*/
void libcrux_sha3_portable_sha512(Eurydice_slice digest, Eurydice_slice data);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 136
*/
void libcrux_sha3_simd_portable_load_block_5b(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 136
*/
void libcrux_sha3_simd_portable_load_block_a1_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
*/
void libcrux_sha3_generic_keccak_absorb_block_80_c60(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 136
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_ad(uint64_t *state,
                                             Eurydice_slice blocks,
                                             size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_a1_ad(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e0(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 136
*/
void libcrux_sha3_simd_portable_store_block_5b(uint64_t *s, Eurydice_slice out,
                                               size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 136
*/
void libcrux_sha3_simd_portable_squeeze_13_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_ad(Eurydice_slice data,
                                                     Eurydice_slice out);

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
void libcrux_sha3_simd_portable_load_last_ad0(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 136
- DELIMITER= 31
*/
void libcrux_sha3_simd_portable_load_last_a1_ad0(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e1(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_portable_keccak1_ad0(Eurydice_slice data,
                                                      Eurydice_slice out);

/**
 A portable SHAKE256 implementation.
*/
void libcrux_sha3_portable_shake256(Eurydice_slice digest, Eurydice_slice data);

typedef libcrux_sha3_generic_keccak_KeccakState_17
    libcrux_sha3_portable_KeccakState;

/**
 Create a new SHAKE-128 state object.
*/
libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake128_init(void);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 168
*/
void libcrux_sha3_simd_portable_load_block_3a(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 168
- DELIMITER= 31
*/
void libcrux_sha3_simd_portable_load_last_c6(uint64_t *state,
                                             Eurydice_slice blocks,
                                             size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 168
- DELIMITER= 31
*/
void libcrux_sha3_simd_portable_load_last_a1_c6(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e2(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
 Absorb
*/
void libcrux_sha3_portable_incremental_shake128_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data0);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 168
*/
void libcrux_sha3_simd_portable_store_block_3a(uint64_t *s, Eurydice_slice out,
                                               size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 168
*/
void libcrux_sha3_simd_portable_squeeze_13_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_three_blocks_b4 with const
generics
- RATE= 168
*/
void libcrux_sha3_generic_keccak_portable_squeeze_first_three_blocks_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out);

/**
 Squeeze three blocks
*/
void libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4 with const generics
- RATE= 168
*/
void libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start);

/**
 Squeeze another block
*/
void libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0);

/**
 Returns the output size of a digest.
*/
size_t libcrux_sha3_digest_size(libcrux_sha3_Algorithm mode);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 144
*/
void libcrux_sha3_simd_portable_load_block_2c(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 144
*/
void libcrux_sha3_simd_portable_load_block_a1_2c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
*/
void libcrux_sha3_generic_keccak_absorb_block_80_c61(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 144
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_1e(uint64_t *state,
                                             Eurydice_slice blocks,
                                             size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 144
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_a1_1e(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 144
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e3(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 144
*/
void libcrux_sha3_simd_portable_store_block_2c(uint64_t *s, Eurydice_slice out,
                                               size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 144
*/
void libcrux_sha3_simd_portable_squeeze_13_2c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_1e(Eurydice_slice data,
                                                     Eurydice_slice out);

/**
 A portable SHA3 224 implementation.
*/
void libcrux_sha3_portable_sha224(Eurydice_slice digest, Eurydice_slice data);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block
with const generics
- RATE= 104
*/
void libcrux_sha3_simd_portable_load_block_7a(uint64_t *state,
                                              Eurydice_slice blocks,
                                              size_t start);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 104
*/
void libcrux_sha3_simd_portable_load_block_a1_7a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
*/
void libcrux_sha3_generic_keccak_absorb_block_80_c62(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last
with const generics
- RATE= 104
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_7c(uint64_t *state,
                                             Eurydice_slice blocks,
                                             size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_last_a1
with const generics
- RATE= 104
- DELIMITER= 6
*/
void libcrux_sha3_simd_portable_load_last_a1_7c(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final_80
with types uint64_t
with const generics
- N= 1
- RATE= 104
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_absorb_final_80_9e4(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.simd.portable.store_block
with const generics
- RATE= 104
*/
void libcrux_sha3_simd_portable_store_block_7a(uint64_t *s, Eurydice_slice out,
                                               size_t start, size_t len);

/**
This function found in impl {libcrux_sha3::traits::Squeeze1<u64> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.squeeze_13
with const generics
- RATE= 104
*/
void libcrux_sha3_simd_portable_squeeze_13_7a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_sha3_generic_keccak_portable_keccak1_7c(Eurydice_slice data,
                                                     Eurydice_slice out);

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
void libcrux_sha3_sha224(Eurydice_slice data, uint8_t ret[28U]);

/**
 SHA3 256
*/
void libcrux_sha3_sha256_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 256
*/
void libcrux_sha3_sha256(Eurydice_slice data, uint8_t ret[32U]);

/**
 SHA3 384
*/
void libcrux_sha3_sha384_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 384
*/
void libcrux_sha3_sha384(Eurydice_slice data, uint8_t ret[48U]);

/**
 SHA3 512
*/
void libcrux_sha3_sha512_ema(Eurydice_slice digest, Eurydice_slice payload);

/**
 SHA3 512
*/
void libcrux_sha3_sha512(Eurydice_slice data, uint8_t ret[64U]);

/**
This function found in impl {libcrux_sha3::traits::Absorb<1usize> for
libcrux_sha3::generic_keccak::KeccakState<u64, 1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of libcrux_sha3.simd.portable.load_block_a1
with const generics
- RATE= 168
*/
void libcrux_sha3_simd_portable_load_block_a1_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *input,
    size_t start);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block_80
with types uint64_t
with const generics
- N= 1
- RATE= 168
*/
void libcrux_sha3_generic_keccak_absorb_block_80_c63(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.portable.keccak1
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_portable_keccak1_c6(Eurydice_slice data,
                                                     Eurydice_slice out);

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
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_five_blocks_b4 with const
generics
- RATE= 168
*/
void libcrux_sha3_generic_keccak_portable_squeeze_first_five_blocks_b4_3a(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out);

/**
 Squeeze five blocks
*/
void libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out0);

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_sha3_portable_incremental_shake256_absorb_final(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice data);

/**
 Create a new SHAKE-256 state object.
*/
libcrux_sha3_generic_keccak_KeccakState_17
libcrux_sha3_portable_incremental_shake256_init(void);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_first_block_b4 with const generics
- RATE= 136
*/
void libcrux_sha3_generic_keccak_portable_squeeze_first_block_b4_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out);

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<u64,
1usize>[core::marker::Sized<u64>,
libcrux_sha3::simd::portable::{libcrux_sha3::traits::KeccakItem<1usize> for
u64}]}
*/
/**
A monomorphic instance of
libcrux_sha3.generic_keccak.portable.squeeze_next_block_b4 with const generics
- RATE= 136
*/
void libcrux_sha3_generic_keccak_portable_squeeze_next_block_b4_5b(
    libcrux_sha3_generic_keccak_KeccakState_17 *self, Eurydice_slice out,
    size_t start);

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
    libcrux_sha3_generic_keccak_KeccakState_17 *s, Eurydice_slice out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $136size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_e2_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][136U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_xof_KeccakXofState_e2;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
    libcrux_sha3_portable_incremental_Shake256Xof;

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.fill_buffer_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
size_t libcrux_sha3_generic_keccak_xof_fill_buffer_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_full_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
size_t libcrux_sha3_generic_keccak_xof_absorb_full_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
void libcrux_sha3_generic_keccak_xof_absorb_35_c6(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs);

/**
 Shake256 absorb
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_sha3_portable_incremental_absorb_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice input);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_final_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
- DELIMITER= 31
*/
void libcrux_sha3_generic_keccak_xof_absorb_final_35_9e(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice *inputs);

/**
 Shake256 absorb final
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_sha3_portable_incremental_absorb_final_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice input);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.zero_block_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
void libcrux_sha3_generic_keccak_xof_zero_block_35_c6(uint8_t ret[136U]);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.new_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 136
*/
libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
libcrux_sha3_generic_keccak_xof_new_35_c6(void);

/**
 Shake256 new state
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
libcrux_sha3_generic_keccak_xof_KeccakXofState_e2
libcrux_sha3_portable_incremental_new_42(void);

/**
 Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
*/
/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, 1usize,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.squeeze_85
with types uint64_t
with const generics
- RATE= 136
*/
void libcrux_sha3_generic_keccak_xof_squeeze_85_c7(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice out);

/**
 Shake256 squeeze
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<136usize>
for libcrux_sha3::portable::incremental::Shake256Xof}
*/
void libcrux_sha3_portable_incremental_squeeze_42(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_e2 *self,
    Eurydice_slice out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.KeccakXofState
with types uint64_t
with const generics
- $1size_t
- $168size_t
*/
typedef struct libcrux_sha3_generic_keccak_xof_KeccakXofState_97_s {
  libcrux_sha3_generic_keccak_KeccakState_17 inner;
  uint8_t buf[1U][168U];
  size_t buf_len;
  bool sponge;
} libcrux_sha3_generic_keccak_xof_KeccakXofState_97;

typedef libcrux_sha3_generic_keccak_xof_KeccakXofState_97
    libcrux_sha3_portable_incremental_Shake128Xof;

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.fill_buffer_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
size_t libcrux_sha3_generic_keccak_xof_fill_buffer_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_full_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
size_t libcrux_sha3_generic_keccak_xof_absorb_full_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
void libcrux_sha3_generic_keccak_xof_absorb_35_c60(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs);

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_sha3_portable_incremental_absorb_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice input);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.absorb_final_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
- DELIMITER= 31
*/
void libcrux_sha3_generic_keccak_xof_absorb_final_35_9e0(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice *inputs);

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_sha3_portable_incremental_absorb_final_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice input);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.zero_block_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
void libcrux_sha3_generic_keccak_xof_zero_block_35_c60(uint8_t ret[168U]);

/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, PARALLEL_LANES,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.new_35
with types uint64_t
with const generics
- PARALLEL_LANES= 1
- RATE= 168
*/
libcrux_sha3_generic_keccak_xof_KeccakXofState_97
libcrux_sha3_generic_keccak_xof_new_35_c60(void);

/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
libcrux_sha3_generic_keccak_xof_KeccakXofState_97
libcrux_sha3_portable_incremental_new_26(void);

/**
 Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
*/
/**
This function found in impl
{libcrux_sha3::generic_keccak::xof::KeccakXofState<STATE, 1usize,
RATE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.xof.squeeze_85
with types uint64_t
with const generics
- RATE= 168
*/
void libcrux_sha3_generic_keccak_xof_squeeze_85_13(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice out);

/**
 Shake128 squeeze
*/
/**
This function found in impl {libcrux_sha3::portable::incremental::Xof<168usize>
for libcrux_sha3::portable::incremental::Shake128Xof}
*/
void libcrux_sha3_portable_incremental_squeeze_26(
    libcrux_sha3_generic_keccak_xof_KeccakXofState_97 *self,
    Eurydice_slice out);

/**
This function found in impl {core::clone::Clone for
libcrux_sha3::portable::KeccakState}
*/
libcrux_sha3_generic_keccak_KeccakState_17 libcrux_sha3_portable_clone_fe(
    libcrux_sha3_generic_keccak_KeccakState_17 *self);

/**
This function found in impl {core::convert::From<libcrux_sha3::Algorithm> for
u32}
*/
uint32_t libcrux_sha3_from_6c(libcrux_sha3_Algorithm v);

/**
This function found in impl {core::convert::From<u32> for
libcrux_sha3::Algorithm}
*/
libcrux_sha3_Algorithm libcrux_sha3_from_29(uint32_t v);

#if defined(__cplusplus)
}
#endif

#define libcrux_sha3_portable_H_DEFINED
#endif /* libcrux_sha3_portable_H */
