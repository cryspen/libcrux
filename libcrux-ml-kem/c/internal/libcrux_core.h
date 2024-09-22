/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
<<<<<<< HEAD
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: 7efec1624422fd5e94388ef06b9c76dfe7a48d46
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: e8928fc5424f83c8cb35b980033be17621fc0ef0
=======
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 97f7cefe14dabf275e4671ffea87e032d7779b71
>>>>>>> main
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
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#13}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_07
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_1f libcrux_ml_kem_types_from_07_a91(
=======
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_40
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_1f libcrux_ml_kem_types_from_40_601(
>>>>>>> main
    uint8_t value[1568U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_64
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
<<<<<<< HEAD
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_64_b11(
=======
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_17_8b1(
>>>>>>> main
    libcrux_ml_kem_types_MlKemPrivateKey_95 sk,
    libcrux_ml_kem_types_MlKemPublicKey_1f pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e7
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_95 libcrux_ml_kem_types_from_e7_f11(
=======
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#10}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_88
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_95 libcrux_ml_kem_types_from_88_2d1(
>>>>>>> main
    uint8_t value[3168U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_15
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext libcrux_ml_kem_types_from_15_e91(
    uint8_t value[1568U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_f6
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_f6_ae1(
    libcrux_ml_kem_types_MlKemPublicKey_1f *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_ba
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_ba_ff1(
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_174(Eurydice_slice slice,
                                                uint8_t ret[1600U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#13}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_07
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_15 libcrux_ml_kem_types_from_07_a90(
=======
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_40
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_15 libcrux_ml_kem_types_from_40_600(
>>>>>>> main
    uint8_t value[1184U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_64
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
<<<<<<< HEAD
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_64_b10(
=======
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_17_8b0(
>>>>>>> main
    libcrux_ml_kem_types_MlKemPrivateKey_55 sk,
    libcrux_ml_kem_types_MlKemPublicKey_15 pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e7
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_55 libcrux_ml_kem_types_from_e7_f10(
=======
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#10}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_88
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_55 libcrux_ml_kem_types_from_88_2d0(
>>>>>>> main
    uint8_t value[2400U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_15
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_15_e90(
    uint8_t value[1088U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_f6
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_f6_ae0(
    libcrux_ml_kem_types_MlKemPublicKey_15 *self);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_ba
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_ba_ff0(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
void libcrux_ml_kem_utils_into_padded_array_173(Eurydice_slice slice,
                                                uint8_t ret[1120U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#13}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_07
with const generics
- SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_be libcrux_ml_kem_types_from_07_a9(
=======
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_40
with const generics
- SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_be libcrux_ml_kem_types_from_40_60(
>>>>>>> main
    uint8_t value[800U]);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_64
with const generics
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
<<<<<<< HEAD
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_types_from_64_b1(
=======
libcrux_ml_kem_types_MlKemKeyPair_cb libcrux_ml_kem_types_from_17_8b(
>>>>>>> main
    libcrux_ml_kem_types_MlKemPrivateKey_5e sk,
    libcrux_ml_kem_types_MlKemPublicKey_be pk);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e7
with const generics
- SIZE= 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey_5e libcrux_ml_kem_types_from_e7_f1(
=======
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#10}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_88
with const generics
- SIZE= 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey_5e libcrux_ml_kem_types_from_88_2d(
>>>>>>> main
    uint8_t value[1632U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_ba
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_ba_121(
    libcrux_ml_kem_types_MlKemPublicKey_15 *self);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
<<<<<<< HEAD
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_15
=======
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fc
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_fc_361(
    uint8_t value[1088U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_fd
>>>>>>> main
with const generics
- SIZE= 1088
*/
<<<<<<< HEAD
libcrux_ml_kem_types_MlKemCiphertext_e8 libcrux_ml_kem_types_from_15_e9(
    uint8_t value[768U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_f6
with const generics
- SIZE= 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_f6_ae(
    libcrux_ml_kem_types_MlKemPublicKey_be *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
=======
Eurydice_slice libcrux_ml_kem_types_as_ref_fd_ed1(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
>>>>>>> main
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
<<<<<<< HEAD
void libcrux_ml_kem_utils_into_padded_array_172(Eurydice_slice slice,
                                                uint8_t ret[33U]);
=======
void libcrux_ml_kem_utils_into_padded_array_425(Eurydice_slice slice,
                                                uint8_t ret[1120U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_ba
with const generics
- SIZE= 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_ba_120(
    libcrux_ml_kem_types_MlKemPublicKey_be *self);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fc
with const generics
- SIZE= 768
*/
libcrux_ml_kem_types_MlKemCiphertext_e8 libcrux_ml_kem_types_from_fc_360(
    uint8_t value[768U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_fd
with const generics
- SIZE= 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_fd_ed0(
    libcrux_ml_kem_types_MlKemCiphertext_e8 *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 800
*/
void libcrux_ml_kem_utils_into_padded_array_424(Eurydice_slice slice,
                                                uint8_t ret[800U]);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_ba
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_ba_12(
    libcrux_ml_kem_types_MlKemPublicKey_1f *self);
>>>>>>> main

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_00_s {
  core_result_Result_86_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_00;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
<<<<<<< HEAD
void core_result_unwrap_41_33(core_result_Result_00 self, uint8_t ret[32U]);
=======
void core_result_unwrap_26_33(core_result_Result_00 self, uint8_t ret[32U]);
>>>>>>> main

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
<<<<<<< HEAD
void libcrux_ml_kem_utils_into_padded_array_171(Eurydice_slice slice,
                                                uint8_t ret[34U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_ba
=======
void libcrux_ml_kem_utils_into_padded_array_422(Eurydice_slice slice,
                                                uint8_t ret[34U]);

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fc
>>>>>>> main
with const generics
- SIZE= 1568
*/
<<<<<<< HEAD
Eurydice_slice libcrux_ml_kem_types_as_ref_ba_ff(
    libcrux_ml_kem_types_MlKemCiphertext_e8 *self);
=======
libcrux_ml_kem_types_MlKemCiphertext_1f libcrux_ml_kem_types_from_fc_36(
    uint8_t value[1568U]);
>>>>>>> main

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
<<<<<<< HEAD
void libcrux_ml_kem_utils_into_padded_array_170(Eurydice_slice slice,
                                                uint8_t ret[800U]);

/**
=======
void libcrux_ml_kem_utils_into_padded_array_421(Eurydice_slice slice,
                                                uint8_t ret[33U]);

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_fd
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_fd_ed(
    libcrux_ml_kem_types_MlKemCiphertext_1f *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_420(Eurydice_slice slice,
                                                uint8_t ret[1600U]);

/**
>>>>>>> main
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
<<<<<<< HEAD
void libcrux_ml_kem_utils_into_padded_array_17(Eurydice_slice slice,
=======
void libcrux_ml_kem_utils_into_padded_array_42(Eurydice_slice slice,
>>>>>>> main
                                               uint8_t ret[64U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_6f_s {
  core_result_Result_86_tags tag;
  union {
    uint8_t case_Ok[24U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_6f;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
<<<<<<< HEAD
void core_result_unwrap_41_76(core_result_Result_6f self, uint8_t ret[24U]);
=======
void core_result_unwrap_26_76(core_result_Result_6f self, uint8_t ret[24U]);
>>>>>>> main

/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_7a_s {
  core_result_Result_86_tags tag;
  union {
    uint8_t case_Ok[20U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_7a;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
<<<<<<< HEAD
void core_result_unwrap_41_ea(core_result_Result_7a self, uint8_t ret[20U]);
=======
void core_result_unwrap_26_ea(core_result_Result_7a self, uint8_t ret[20U]);
>>>>>>> main

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_cd_s {
  core_result_Result_86_tags tag;
  union {
    uint8_t case_Ok[10U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_cd;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
<<<<<<< HEAD
void core_result_unwrap_41_07(core_result_Result_cd self, uint8_t ret[10U]);
=======
void core_result_unwrap_26_07(core_result_Result_cd self, uint8_t ret[10U]);
>>>>>>> main

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_c0_s {
  core_result_Result_86_tags tag;
  union {
    int16_t case_Ok[16U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_c0;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
<<<<<<< HEAD
void core_result_unwrap_41_30(core_result_Result_c0 self, int16_t ret[16U]);
=======
void core_result_unwrap_26_30(core_result_Result_c0 self, int16_t ret[16U]);
>>>>>>> main

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_core_H_DEFINED
#endif
