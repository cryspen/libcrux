/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3275bf4ad9dc8c25965dc5da6122653fc43c4287
 * Eurydice: d3b14228e2b5fe8710ec7efae31e4de2c96ed20d
 * Karamel: 095cdb73f246711f93f99a159ceca37cd2c227e1
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 75cbe9ea0e459cf8a62d97e8a867411e0dd8529a
 */

#ifndef __internal_libcrux_core_H
#define __internal_libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_core.h"

#define CORE_NUM__U32_8__BITS (32U)

static inline uint32_t core_num__u8_6__count_ones(uint8_t x0);

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

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

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_73_39(int16_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
uint8_t libcrux_secrets_int_as_u8_d2(int16_t self);

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_57_39(int16_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u8)}
*/
int16_t libcrux_secrets_int_as_i16_84(uint8_t self);

int16_t libcrux_secrets_int_I16(int16_t v);

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
int32_t libcrux_secrets_int_as_i32_d2(int16_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for i32)#6}
*/
int16_t libcrux_secrets_int_as_i16_98(int32_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
int32_t libcrux_secrets_int_as_i32_41(uint32_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
uint16_t libcrux_secrets_int_as_u16_d2(int16_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
int16_t libcrux_secrets_int_as_i16_e9(uint16_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
uint64_t libcrux_secrets_int_as_u64_e9(uint16_t self);

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_57_df(uint32_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u64)#3}
*/
uint32_t libcrux_secrets_int_as_u32_0b(uint64_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
int16_t libcrux_secrets_int_as_i16_41(uint32_t self);

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
int16_t libcrux_secrets_int_as_i16_d2(int16_t self);

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

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_3a_94(
    libcrux_ml_kem_types_MlKemPrivateKey_83 sk,
    libcrux_ml_kem_types_MlKemPublicKey_64 pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_83 libcrux_ml_kem_types_from_9a_39(
    uint8_t value[3168U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_af(
    libcrux_ml_kem_types_MlKemCiphertext_64 *self);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_3a_74(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 sk,
    libcrux_ml_kem_types_MlKemPublicKey_30 pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_d9 libcrux_ml_kem_types_from_9a_28(
    uint8_t value[2400U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1088
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemKeyPair_3e libcrux_ml_kem_types_from_3a_fa(
    libcrux_ml_kem_types_MlKemPrivateKey_fa sk,
    libcrux_ml_kem_types_MlKemPublicKey_52 pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey_fa libcrux_ml_kem_types_from_9a_2a(
    uint8_t value[1632U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 768
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_d0(
    libcrux_ml_kem_types_MlKemCiphertext_1a *self);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_d0(
    libcrux_ml_kem_types_MlKemPublicKey_30 *self);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_30 libcrux_ml_kem_types_from_5f_d0(
    uint8_t value[1184U]);

typedef struct Eurydice_slice_uint8_t_x4_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
  Eurydice_slice thd;
  Eurydice_slice f3;
} Eurydice_slice_uint8_t_x4;

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_b4(
    Eurydice_slice private_key);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_00_80(
    uint8_t value[1088U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
void libcrux_ml_kem_utils_into_padded_array_15(Eurydice_slice slice,
                                               uint8_t ret[1120U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_4d(
    libcrux_ml_kem_types_MlKemPublicKey_52 *self);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_52 libcrux_ml_kem_types_from_5f_4d(
    uint8_t value[800U]);

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_0c(
    Eurydice_slice private_key);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 768
*/
libcrux_ml_kem_types_MlKemCiphertext_1a libcrux_ml_kem_types_from_00_d0(
    uint8_t value[768U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 2
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_fd(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_d0(
    libcrux_ml_kem_types_MlKemCiphertext_1a *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 800
*/
void libcrux_ml_kem_utils_into_padded_array_4d(Eurydice_slice slice,
                                               uint8_t ret[800U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_af(
    libcrux_ml_kem_types_MlKemPublicKey_64 *self);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_64 libcrux_ml_kem_types_from_5f_af(
    uint8_t value[1568U]);

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_1f(
    Eurydice_slice private_key);

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_fb_s {
  core_result_Result_a9_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_fb;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_b3(core_result_Result_fb self, uint8_t ret[32U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
void libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_slice slice,
                                               uint8_t ret[34U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemCiphertext_64 libcrux_ml_kem_types_from_00_af(
    uint8_t value[1568U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_ac(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
void libcrux_ml_kem_utils_into_padded_array_c8(Eurydice_slice slice,
                                               uint8_t ret[33U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_af(
    libcrux_ml_kem_types_MlKemCiphertext_64 *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_slice slice,
                                               uint8_t ret[1600U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
void libcrux_ml_kem_utils_into_padded_array_24(Eurydice_slice slice,
                                               uint8_t ret[64U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_b2_s {
  core_result_Result_a9_tags tag;
  union {
    uint8_t case_Ok[24U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_b2;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_70(core_result_Result_b2 self, uint8_t ret[24U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_e1_s {
  core_result_Result_a9_tags tag;
  union {
    uint8_t case_Ok[20U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_e1;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_20(core_result_Result_e1 self, uint8_t ret[20U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_9d_s {
  core_result_Result_a9_tags tag;
  union {
    uint8_t case_Ok[10U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_9d;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_ce(core_result_Result_9d self, uint8_t ret[10U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[24size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_d2(uint8_t self[24U],
                                                          uint8_t ret[24U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[20size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_57(uint8_t self[20U],
                                                          uint8_t ret[20U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[10size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_cc(uint8_t self[10U],
                                                          uint8_t ret[10U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[8size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_76(uint8_t self[8U],
                                                          uint8_t ret[8U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[2size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_d4(uint8_t self[2U],
                                                          uint8_t ret[2U]);

/**
 Classify a mutable slice (identity)
 We define a separate function for this because hax has limited support for
 &mut-returning functions
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_mut_slice
with types Eurydice_slice uint8_t

*/
Eurydice_slice libcrux_secrets_int_public_integers_classify_mut_slice_ba(
    Eurydice_slice x);

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_classify_57_46(int16_t self[16U],
                                                        int16_t ret[16U]);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_46(int16_t self[16U],
                                                          int16_t ret[16U]);

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice uint8_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_b8_ba(
    Eurydice_slice *self);

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[22size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_fa(uint8_t self[22U],
                                                          uint8_t ret[22U]);

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice int16_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_b8_03(
    Eurydice_slice *self);

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_0a_s {
  core_result_Result_a9_tags tag;
  union {
    int16_t case_Ok[16U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_0a;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_00(core_result_Result_0a self, int16_t ret[16U]);

typedef struct Eurydice_slice_uint8_t_200size_t__x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_200size_t__x2;

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
