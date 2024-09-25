/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 97f7cefe14dabf275e4671ffea87e032d7779b71
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
typedef struct core_ops_range_Range_b3_s {
  size_t start;
  size_t end;
} core_ops_range_Range_b3;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_86_tags;

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option_ef_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct core_option_Option_b3_s {
  core_option_Option_ef_tags tag;
  size_t f0;
} core_option_Option_b3;

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_1f_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemPublicKey_1f;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $3168size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_95_s {
  uint8_t value[3168U];
} libcrux_ml_kem_types_MlKemPrivateKey_95;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_95 sk;
  libcrux_ml_kem_types_MlKemPublicKey_1f pk;
} libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_15_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_15;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_55_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey_55;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_55 sk;
  libcrux_ml_kem_types_MlKemPublicKey_15 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_be_s {
  uint8_t value[800U];
} libcrux_ml_kem_types_MlKemPublicKey_be;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $1632size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_5e_s {
  uint8_t value[1632U];
} libcrux_ml_kem_types_MlKemPrivateKey_5e;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemKeyPair
with const generics
- $1632size_t
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemKeyPair_cb_s {
  libcrux_ml_kem_types_MlKemPrivateKey_5e sk;
  libcrux_ml_kem_types_MlKemPublicKey_be pk;
} libcrux_ml_kem_types_MlKemKeyPair_cb;

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_3c_s {
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} tuple_3c;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $768size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_e8_s {
  uint8_t value[768U];
} libcrux_ml_kem_types_MlKemCiphertext_e8;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$768size_t]], uint8_t[32size_t]

*/
typedef struct tuple_ec_s {
  libcrux_ml_kem_types_MlKemCiphertext_e8 fst;
  uint8_t snd[32U];
} tuple_ec;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_1f_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemCiphertext_1f;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1568size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_21_s {
  libcrux_ml_kem_types_MlKemCiphertext_1f fst;
  uint8_t snd[32U];
} tuple_21;

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_56_s {
  core_result_Result_86_tags tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_56;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_0e(core_result_Result_56 self, uint8_t ret[8U]);

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
