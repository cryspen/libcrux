/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: b351338f6a84c7a1afc27433eb0ffdc668b3581d
 * Eurydice: fcdd1852994390db2b6aa780ed8d837fa811167d
 * Karamel: c96fb69d15693284644d6aecaa90afa37e4de8f0
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: 7cd7a08d172e1715493176358bffadf8f87ae3a4
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

static inline int16_t core_num__i16_1__wrapping_add(int16_t x0, int16_t x1);

static inline int16_t core_num__i16_1__wrapping_mul(int16_t x0, int16_t x1);

static inline int16_t core_num__i16_1__wrapping_sub(int16_t x0, int16_t x1);

static inline uint16_t core_num__u16_7__wrapping_add(uint16_t x0, uint16_t x1);

#define CORE_NUM__U32_8__BITS (32U)

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

static inline uint32_t core_num__u8_6__count_ones(uint8_t x0);

static inline uint8_t core_num__u8_6__wrapping_sub(uint8_t x0, uint8_t x1);

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  uint8_t fst[1152U];
  uint8_t snd[1184U];
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_6f_tags;

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_6f_s {
  core_result_Result_6f_tags tag;
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
static inline void core_result_unwrap_41_76(core_result_Result_6f self,
                                            uint8_t ret[24U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[24U];
    memcpy(f0, self.val.case_Ok, (size_t)24U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)24U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_7a_s {
  core_result_Result_6f_tags tag;
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
static inline void core_result_unwrap_41_ea(core_result_Result_7a self,
                                            uint8_t ret[20U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[20U];
    memcpy(f0, self.val.case_Ok, (size_t)20U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)20U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_cd_s {
  core_result_Result_6f_tags tag;
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
static inline void core_result_unwrap_41_07(core_result_Result_cd self,
                                            uint8_t ret[10U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[10U];
    memcpy(f0, self.val.case_Ok, (size_t)10U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)10U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_15_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_15;

/**
A monomorphic instance of core.option.Option
with types libcrux_ml_kem_types_MlKemPublicKey[[$1184size_t]]

*/
typedef struct core_option_Option_92_s {
  core_option_Option_ef_tags tag;
  libcrux_ml_kem_types_MlKemPublicKey_15 f0;
} core_option_Option_92;

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_a8
with const generics
- SIZE= 1088
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_a8_2f(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#13}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_07
with const generics
- SIZE= 1184
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_15
libcrux_ml_kem_types_from_07_78(uint8_t value[1184U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1184U];
  memcpy(copy_of_value, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_15 lit;
  memcpy(lit.value, copy_of_value, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

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
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_64
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_64_00(libcrux_ml_kem_types_MlKemPrivateKey_55 sk,
                                libcrux_ml_kem_types_MlKemPublicKey_15 pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk, .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e7
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_55
libcrux_ml_kem_types_from_e7_1d(uint8_t value[2400U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2400U];
  memcpy(copy_of_value, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 lit;
  memcpy(lit.value, copy_of_value, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

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
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_15
with const generics
- SIZE= 1088
*/
static inline libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types_from_15_89(uint8_t value[1088U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1088U];
  memcpy(copy_of_value, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, copy_of_value, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_f6
with const generics
- SIZE= 1184
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_f6_7b(
    libcrux_ml_kem_types_MlKemPublicKey_15 *self) {
  return self->value;
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_172(
    Eurydice_slice slice, uint8_t ret[33U]) {
  uint8_t out[33U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)33U * sizeof(uint8_t));
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_00_s {
  core_result_Result_6f_tags tag;
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
static inline void core_result_unwrap_41_33(core_result_Result_00 self,
                                            uint8_t ret[32U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[32U];
    memcpy(f0, self.val.case_Ok, (size_t)32U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)32U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_171(
    Eurydice_slice slice, uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_ba
with const generics
- SIZE= 1088
*/
static inline Eurydice_slice libcrux_ml_kem_types_as_ref_ba_f1(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1088U, self->value, uint8_t);
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_170(
    Eurydice_slice slice, uint8_t ret[1120U]) {
  uint8_t out[1120U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)1120U * sizeof(uint8_t));
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_17(
    Eurydice_slice slice, uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_c0_s {
  core_result_Result_6f_tags tag;
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
static inline void core_result_unwrap_41_30(core_result_Result_c0 self,
                                            int16_t ret[16U]) {
  if (self.tag == core_result_Ok) {
    int16_t f0[16U];
    memcpy(f0, self.val.case_Ok, (size_t)16U * sizeof(int16_t));
    memcpy(ret, f0, (size_t)16U * sizeof(int16_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_56_s {
  core_result_Result_6f_tags tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_56;

/**
This function found in impl {core::result::Result<T, E>}
*/
/**
A monomorphic instance of core.result.unwrap_41
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
static inline void core_result_unwrap_41_0e(core_result_Result_56 self,
                                            uint8_t ret[8U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[8U];
    memcpy(f0, self.val.case_Ok, (size_t)8U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)8U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

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
