/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: d6e4d1bb9c27c4eebbebcb29ba8bea1d58741421
 * Karamel: 2bd16e63cfbfa2b81d3c45d597b811ca2a12d430
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: a7de672380a622d67efb35e3707a528e375cbf76
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

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_1f libcrux_ml_kem_types_from_b6_571(
    uint8_t value[1568U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_17_2c1(
    libcrux_ml_kem_types_MlKemPrivateKey_95 sk,
    libcrux_ml_kem_types_MlKemPublicKey_1f pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_95 libcrux_ml_kem_types_from_05_e01(
    uint8_t value[3168U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext libcrux_ml_kem_types_from_01_201(
    uint8_t value[1568U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_1f1(
    libcrux_ml_kem_types_MlKemPublicKey_1f *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_f01(
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_974(Eurydice_slice slice,
                                                uint8_t ret[1600U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_15 libcrux_ml_kem_types_from_b6_570(
    uint8_t value[1184U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_17_2c0(
    libcrux_ml_kem_types_MlKemPrivateKey_55 sk,
    libcrux_ml_kem_types_MlKemPublicKey_15 pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_55 libcrux_ml_kem_types_from_05_e00(
    uint8_t value[2400U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_01_200(
    uint8_t value[1088U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_1f0(
    libcrux_ml_kem_types_MlKemPublicKey_15 *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_f00(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
void libcrux_ml_kem_utils_into_padded_array_973(Eurydice_slice slice,
                                                uint8_t ret[1120U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6
with const generics
- SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_be libcrux_ml_kem_types_from_b6_57(
    uint8_t value[800U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_types_from_17_2c(
    libcrux_ml_kem_types_MlKemPrivateKey_5e sk,
    libcrux_ml_kem_types_MlKemPublicKey_be pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05
with const generics
- SIZE= 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey_5e libcrux_ml_kem_types_from_05_e0(
    uint8_t value[1632U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01
with const generics
- SIZE= 768
*/
libcrux_ml_kem_types_MlKemCiphertext_e8 libcrux_ml_kem_types_from_01_20(
    uint8_t value[768U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb
with const generics
- SIZE= 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_1f(
    libcrux_ml_kem_types_MlKemPublicKey_be *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
void libcrux_ml_kem_utils_into_padded_array_972(Eurydice_slice slice,
                                                uint8_t ret[33U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_00_s {
  core_result_Result_00_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_00;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_41_83(core_result_Result_00 self, uint8_t ret[32U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
void libcrux_ml_kem_utils_into_padded_array_971(Eurydice_slice slice,
                                                uint8_t ret[34U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00
with const generics
- SIZE= 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_f0(
    libcrux_ml_kem_types_MlKemCiphertext_e8 *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 800
*/
void libcrux_ml_kem_utils_into_padded_array_970(Eurydice_slice slice,
                                                uint8_t ret[800U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
void libcrux_ml_kem_utils_into_padded_array_97(Eurydice_slice slice,
                                               uint8_t ret[64U]);

/**
A monomorphic instance of core.option.Option
with types Eurydice_slice uint8_t

*/
typedef struct core_option_Option_44_s {
  core_option_Option_ef_tags tag;
  Eurydice_slice f0;
} core_option_Option_44;

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_6f_s {
  core_result_Result_00_tags tag;
  union {
    uint8_t case_Ok[24U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_6f;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_41_1c(core_result_Result_6f self, uint8_t ret[24U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_7a_s {
  core_result_Result_00_tags tag;
  union {
    uint8_t case_Ok[20U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_7a;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_41_34(core_result_Result_7a self, uint8_t ret[20U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_cd_s {
  core_result_Result_00_tags tag;
  union {
    uint8_t case_Ok[10U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_cd;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_41_e8(core_result_Result_cd self, uint8_t ret[10U]);

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_c0_s {
  core_result_Result_00_tags tag;
  union {
    int16_t case_Ok[16U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_c0;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types int16_t[16size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_41_f9(core_result_Result_c0 self, int16_t ret[16U]);

typedef struct Eurydice_slice_uint8_t_2size_t__x2_s {
  Eurydice_slice fst[2U];
  Eurydice_slice snd[2U];
} Eurydice_slice_uint8_t_2size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
