/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45f5a34f336e35c6cc2253bc90cbdb8d812cefa9
 * Eurydice: e2db6e88adc9995ca9d3dedf7fa9bc4095e9ca20
 * Karamel: 8c3612018c25889288da6857771be3ad03b75bcd
 * F*: 5643e656b989aca7629723653a2570c7df6252b9
 * Libcrux: fbef3649fa222b800fc7dcc349855bcd7de48e36
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

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
