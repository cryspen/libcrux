/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: bba1aa4cae0326f1d94d466f8263e85dd9f14efe
 * Eurydice: 9f45c5b6710ac03aa157299391233be90bc1565c
 * Karamel: b7bdca21d1dbfd635f6ff432c0d8da3d5ca2edbc
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: e023f8453e3c2f240705192cb557223357129b0d
 */

#ifndef __internal_libcrux_sha3_avx2_H
#define __internal_libcrux_sha3_avx2_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_sha3_avx2.h"

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
libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_generic_keccak_new_89_a6(void);

/**
A monomorphic instance of libcrux_sha3.traits.set_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_traits_set_ij_a6(__m256i *arr, size_t i, size_t j,
                                   __m256i value);

/**
A monomorphic instance of libcrux_sha3.traits.get_ij
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
__m256i libcrux_sha3_traits_get_ij_a6(__m256i *arr, size_t i, size_t j);

/**
This function found in impl {libcrux_sha3::generic_keccak::KeccakState<T,
N>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.get_80
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
__m256i libcrux_sha3_generic_keccak_get_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t i, size_t j);

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
void libcrux_sha3_generic_keccak_set_80_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self, size_t i, size_t j,
    __m256i v);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.theta_rho
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_generic_keccak_theta_rho_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s);

/**
This function found in impl {(core::clone::Clone for
libcrux_sha3::generic_keccak::KeccakState<T, N>[TraitClause@0,
TraitClause@2])#3}
*/
/**
A monomorphic instance of libcrux_sha3.generic_keccak.clone_db
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
libcrux_sha3_generic_keccak_KeccakState_55
libcrux_sha3_generic_keccak_clone_db_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *self);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.pi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_generic_keccak_pi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.chi
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_generic_keccak_chi_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.iota
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_generic_keccak_iota_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, size_t i);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccakf1600
with types core_core_arch_x86___m256i
with const generics
- N= 4
*/
void libcrux_sha3_generic_keccak_keccakf1600_a6(
    libcrux_sha3_generic_keccak_KeccakState_55 *s);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
void libcrux_sha3_generic_keccak_absorb_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_absorb_final_fb(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_and_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
void libcrux_sha3_generic_keccak_squeeze_first_and_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
void libcrux_sha3_generic_keccak_squeeze_first_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
void libcrux_sha3_generic_keccak_squeeze_next_block_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_last
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
*/
void libcrux_sha3_generic_keccak_squeeze_last_97(
    libcrux_sha3_generic_keccak_KeccakState_55 s, Eurydice_slice out[4U]);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.keccak
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 136
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_keccak_fb(Eurydice_slice *data,
                                           Eurydice_slice out[4U]);

typedef libcrux_sha3_generic_keccak_KeccakState_55
    libcrux_sha3_avx2_x4_incremental_KeccakState;

/**
A monomorphic instance of libcrux_sha3.generic_keccak.absorb_final
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
- DELIM= 31
*/
void libcrux_sha3_generic_keccak_absorb_final_fb0(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
void libcrux_sha3_generic_keccak_squeeze_first_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_next_block
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
void libcrux_sha3_generic_keccak_squeeze_next_block_970(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice *out);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_three_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
void libcrux_sha3_generic_keccak_squeeze_first_three_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]);

/**
A monomorphic instance of libcrux_sha3.generic_keccak.squeeze_first_five_blocks
with types core_core_arch_x86___m256i
with const generics
- N= 4
- RATE= 168
*/
void libcrux_sha3_generic_keccak_squeeze_first_five_blocks_97(
    libcrux_sha3_generic_keccak_KeccakState_55 *s, Eurydice_slice out[4U]);

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_sha3_avx2_H_DEFINED
#endif
