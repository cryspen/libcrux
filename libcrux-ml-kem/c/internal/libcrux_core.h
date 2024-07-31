/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 013beb9e4046a151131c6a56dfe25e606b49c4a1
 * Karamel: 4626e5fcb3787a47c806d160539342ade4b0809c
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: a0db75c27aa09b79eae1c2315196383465857308
 */

#ifndef __internal_libcrux_core_H
#define __internal_libcrux_core_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_core.h"
#include "eurydice_glue.h"

#define CORE_NUM__U32_8__BITS (32U)

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
A monomorphic instance of libcrux_ml_kem.types.from_b6 with const generics:
- SIZE = 800
*/
libcrux_ml_kem_types_MlKemPublicKey____800size_t
libcrux_ml_kem_types_from_b6_72(uint8_t value[800U]);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17 with const generics:
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
*/
libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_types_from_17_8e0(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____800size_t pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05 with const generics:
- SIZE = 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey____1632size_t
libcrux_ml_kem_types_from_05_e0(uint8_t value[1632U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01 with const generics:
- SIZE = 768
*/
libcrux_ml_kem_types_MlKemCiphertext____768size_t
libcrux_ml_kem_types_from_01_e3(uint8_t value[768U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb with const generics:
- SIZE = 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_72(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00 with const generics:
- SIZE = 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_e3(
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *self);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 800
*/
void libcrux_ml_kem_utils_into_padded_array_72(Eurydice_slice slice,
                                               uint8_t ret[800U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6 with const generics:
- SIZE = 1568
*/
libcrux_ml_kem_types_MlKemPublicKey____1568size_t
libcrux_ml_kem_types_from_b6_a7(uint8_t value[1568U]);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17 with const generics:
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_17_8e(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05 with const generics:
- SIZE = 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey____3168size_t
libcrux_ml_kem_types_from_05_df(uint8_t value[3168U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01 with const generics:
- SIZE = 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext libcrux_ml_kem_types_from_01_a7(
    uint8_t value[1568U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb with const generics:
- SIZE = 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_a7(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00 with const generics:
- SIZE = 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_a7(
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *self);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 1600
*/
void libcrux_ml_kem_utils_into_padded_array_cd(Eurydice_slice slice,
                                               uint8_t ret[1600U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6 with const generics:
- SIZE = 1184
*/
libcrux_ml_kem_types_MlKemPublicKey____1184size_t
libcrux_ml_kem_types_from_b6_fb(uint8_t value[1184U]);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17 with const generics:
- PRIVATE_KEY_SIZE = 2400
- PUBLIC_KEY_SIZE = 1184
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_17_b5(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05 with const generics:
- SIZE = 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey____2400size_t
libcrux_ml_kem_types_from_05_99(uint8_t value[2400U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01 with const generics:
- SIZE = 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_01_e6(
    uint8_t value[1088U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb with const generics:
- SIZE = 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_cb_fb(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *self);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 33
*/
void libcrux_ml_kem_utils_into_padded_array_cb(Eurydice_slice slice,
                                               uint8_t ret[33U]);

typedef struct
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41 with types uint8_t[32size_t],
core_array_TryFromSliceError
*/
void core_result_unwrap_41_fb(
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError self,
    uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 34
*/
void libcrux_ml_kem_utils_into_padded_array_fe(Eurydice_slice slice,
                                               uint8_t ret[34U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00 with const generics:
- SIZE = 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_00_e6(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 1120
*/
void libcrux_ml_kem_utils_into_padded_array_a0(Eurydice_slice slice,
                                               uint8_t ret[1120U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array with const
generics:
- LEN = 64
*/
void libcrux_ml_kem_utils_into_padded_array_51(Eurydice_slice slice,
                                               uint8_t ret[64U]);

typedef struct core_option_Option__Eurydice_slice_uint8_t_s {
  core_option_Option__int32_t_tags tag;
  Eurydice_slice f0;
} core_option_Option__Eurydice_slice_uint8_t;

typedef struct
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError_s {
  core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_tags tag;
  union {
    int16_t case_Ok[16U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result__int16_t_16size_t__core_array_TryFromSliceError;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41 with types int16_t[16size_t],
core_array_TryFromSliceError
*/
void core_result_unwrap_41_0a(
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError self,
    int16_t ret[16U]);

typedef struct
    K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t__s {
  Eurydice_slice fst[2U];
  Eurydice_slice snd[2U];
} K___Eurydice_slice_uint8_t_2size_t__Eurydice_slice_uint8_t_2size_t_;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
