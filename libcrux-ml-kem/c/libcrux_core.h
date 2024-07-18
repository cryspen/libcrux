/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0f1b5e50fa4e96ed9e650d8334e1afbf2bf319b1
 * Eurydice: f415f299462ee62cdddcb42ae16b10bb6a7e4f0a
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: fd115e1b6265143551fbd8d7924c933d055de75d
 */

#ifndef __libcrux_core_H
#define __libcrux_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

typedef struct core_ops_range_Range__size_t_s {
  size_t start;
  size_t end;
} core_ops_range_Range__size_t;

extern uint8_t Eurydice_bitand_pv_u8(uint8_t *x, uint8_t y);

extern uint8_t Eurydice_shr_pv_u8(uint8_t *x, int32_t y);

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option__int32_t_tags;

typedef struct core_option_Option__size_t_s {
  core_option_Option__int32_t_tags tag;
  size_t f0;
} core_option_Option__size_t;

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

typedef struct libcrux_ml_kem_types_MlKemPublicKey____1568size_t_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemPublicKey____1568size_t;

typedef struct
    core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t___s {
  core_option_Option__int32_t_tags tag;
  libcrux_ml_kem_types_MlKemPublicKey____1568size_t f0;
} core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__;

typedef struct libcrux_ml_kem_types_MlKemPrivateKey____3168size_t_s {
  uint8_t value[3168U];
} libcrux_ml_kem_types_MlKemPrivateKey____3168size_t;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey____3168size_t sk;
  libcrux_ml_kem_types_MlKemPublicKey____1568size_t pk;
} libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext_s {
  uint8_t value[1568U];
} libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext;

typedef struct
    K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t__s {
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext fst;
  uint8_t snd[32U];
} K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_;

typedef struct libcrux_ml_kem_types_MlKemPublicKey____1184size_t_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey____1184size_t;

typedef struct
    core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1184size_t___s {
  core_option_Option__int32_t_tags tag;
  libcrux_ml_kem_types_MlKemPublicKey____1184size_t f0;
} core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1184size_t__;

typedef struct libcrux_ml_kem_types_MlKemPrivateKey____2400size_t_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey____2400size_t;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey____2400size_t sk;
  libcrux_ml_kem_types_MlKemPublicKey____1184size_t pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

typedef struct
    K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t__s {
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_;

typedef struct libcrux_ml_kem_types_MlKemPublicKey____800size_t_s {
  uint8_t value[800U];
} libcrux_ml_kem_types_MlKemPublicKey____800size_t;

typedef struct
    core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t___s {
  core_option_Option__int32_t_tags tag;
  libcrux_ml_kem_types_MlKemPublicKey____800size_t f0;
} core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__;

typedef struct libcrux_ml_kem_types_MlKemPrivateKey____1632size_t_s {
  uint8_t value[1632U];
} libcrux_ml_kem_types_MlKemPrivateKey____1632size_t;

typedef struct libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t_s {
  libcrux_ml_kem_types_MlKemPrivateKey____1632size_t sk;
  libcrux_ml_kem_types_MlKemPublicKey____800size_t pk;
} libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t;

typedef struct libcrux_ml_kem_types_MlKemCiphertext____768size_t_s {
  uint8_t value[768U];
} libcrux_ml_kem_types_MlKemCiphertext____768size_t;

typedef struct
    K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t__s {
  libcrux_ml_kem_types_MlKemCiphertext____768size_t fst;
  uint8_t snd[32U];
} K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags;

typedef struct
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__uint8_t_8size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError self,
    uint8_t ret[8U]);

typedef struct K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} K___Eurydice_slice_uint8_t_Eurydice_slice_uint8_t;

typedef struct
    K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t__s {
  Eurydice_slice fst[1U];
  Eurydice_slice snd[1U];
} K___Eurydice_slice_uint8_t_1size_t__Eurydice_slice_uint8_t_1size_t_;

#if defined(__cplusplus)
}
#endif

#define __libcrux_core_H_DEFINED
#endif
