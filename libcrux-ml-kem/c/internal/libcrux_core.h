/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 4d6cf6308cb714aadcd1df0ba5f71977ec6c4a99
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: c9c098bdea22047a1eb811ddf3468543855da224
 */

#ifndef __internal_libcrux_core_H
#define __internal_libcrux_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_core.h"
#include "eurydice_glue.h"

#define CORE_NUM__U32_8__BITS (32U)

static inline uint32_t core_num__u8_6__count_ones(uint8_t x0);

uint8_t libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs);

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

void libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector, uint8_t ret[32U]);

void libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s, uint8_t ret[32U]);

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair1024_s {
  uint8_t fst[1536U];
  uint8_t snd[1568U];
} libcrux_ml_kem_utils_extraction_helper_Keypair1024;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair512_s {
  uint8_t fst[768U];
  uint8_t snd[800U];
} libcrux_ml_kem_utils_extraction_helper_Keypair512;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  uint8_t fst[1152U];
  uint8_t snd[1184U];
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

libcrux_ml_kem_types_MlKemPublicKey____1568size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1568size_t(
    uint8_t value[1568U]);

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___3168size_t_1568size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t pk);

libcrux_ml_kem_types_MlKemPrivateKey____3168size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___3168size_t(
    uint8_t value[3168U]);

libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1568size_t(
    uint8_t value[1568U]);

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1568size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *self);

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *self);

void libcrux_ml_kem_utils_into_padded_array___1600size_t(Eurydice_slice slice,
                                                         uint8_t ret[1600U]);

libcrux_ml_kem_types_MlKemPublicKey____1184size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1184size_t(
    uint8_t value[1184U]);

libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___2400size_t_1184size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t pk);

libcrux_ml_kem_types_MlKemPrivateKey____2400size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___2400size_t(
    uint8_t value[2400U]);

libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1088size_t(
    uint8_t value[1088U]);

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1184size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *self);

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

void libcrux_ml_kem_utils_into_padded_array___1120size_t(Eurydice_slice slice,
                                                         uint8_t ret[1120U]);

libcrux_ml_kem_types_MlKemPublicKey____800size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___800size_t(
    uint8_t value[800U]);

libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___1632size_t_800size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____800size_t pk);

libcrux_ml_kem_types_MlKemPrivateKey____1632size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___1632size_t(
    uint8_t value[1632U]);

libcrux_ml_kem_types_MlKemCiphertext____768size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___768size_t(
    uint8_t value[768U]);

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___800size_t(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *self);

void libcrux_ml_kem_utils_into_padded_array___33size_t(Eurydice_slice slice,
                                                       uint8_t ret[33U]);

typedef struct
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError self,
    uint8_t ret[32U]);

void libcrux_ml_kem_utils_into_padded_array___34size_t(Eurydice_slice slice,
                                                       uint8_t ret[34U]);

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *self);

void libcrux_ml_kem_utils_into_padded_array___800size_t(Eurydice_slice slice,
                                                        uint8_t ret[800U]);

void libcrux_ml_kem_utils_into_padded_array___64size_t(Eurydice_slice slice,
                                                       uint8_t ret[64U]);

typedef struct
    core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[24U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__uint8_t_24size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError self,
    uint8_t ret[24U]);

typedef struct
    core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[20U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__uint8_t_20size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError self,
    uint8_t ret[20U]);

typedef struct
    core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[10U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__uint8_t_10size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError self,
    uint8_t ret[10U]);

typedef struct
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    int16_t case_Ok[16U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__int16_t_16size_t__core_array_TryFromSliceError;

void core_result__core__result__Result_T__E___unwrap__int16_t_16size_t__core_array_TryFromSliceError(
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError self,
    int16_t ret[16U]);

typedef struct
    K___Eurydice_slice_uint8_t_4size_t__Eurydice_slice_uint8_t_4size_t__s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} K___Eurydice_slice_uint8_t_4size_t__Eurydice_slice_uint8_t_4size_t_;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
