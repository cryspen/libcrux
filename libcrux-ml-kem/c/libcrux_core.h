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

#ifndef __libcrux_core_H
#define __libcrux_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_a9_tags;

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option_9e_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct core_option_Option_08_s {
  core_option_Option_9e_tags tag;
  size_t f0;
} core_option_Option_08;

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_64_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemPublicKey_64;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $3168size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_83_s {
  uint8_t value[3168U];
} libcrux_ml_kem_types_MlKemPrivateKey_83;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_83 sk;
  libcrux_ml_kem_types_MlKemPublicKey_64 pk;
} libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_30_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_30;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_d9_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey_d9;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_ml_kem_types_MlKemPublicKey_30 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_52_s {
  uint8_t value[800U];
} libcrux_ml_kem_types_MlKemPublicKey_52;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $1632size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_fa_s {
  uint8_t value[1632U];
} libcrux_ml_kem_types_MlKemPrivateKey_fa;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemKeyPair
with const generics
- $1632size_t
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemKeyPair_3e_s {
  libcrux_ml_kem_types_MlKemPrivateKey_fa sk;
  libcrux_ml_kem_types_MlKemPublicKey_52 pk;
} libcrux_ml_kem_types_MlKemKeyPair_3e;

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_c2_s {
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} tuple_c2;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $768size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_1a_s {
  uint8_t value[768U];
} libcrux_ml_kem_types_MlKemCiphertext_1a;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$768size_t]], uint8_t[32size_t]

*/
typedef struct tuple_41_s {
  libcrux_ml_kem_types_MlKemCiphertext_1a fst;
  uint8_t snd[32U];
} tuple_41;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_64_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemCiphertext_64;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1568size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_fa_s {
  libcrux_ml_kem_types_MlKemCiphertext_64 fst;
  uint8_t snd[32U];
} tuple_fa;

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_15_s {
  core_result_Result_a9_tags tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_15;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_68(core_result_Result_15 self, uint8_t ret[8U]);

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

typedef struct Eurydice_slice_uint8_t_1size_t__x2_s {
  Eurydice_slice fst[1U];
  Eurydice_slice snd[1U];
} Eurydice_slice_uint8_t_1size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __libcrux_core_H_DEFINED
#endif
