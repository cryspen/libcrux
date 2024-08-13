/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
<<<<<<< HEAD
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: ab466d75991f78bb7925bf97c8ee9874f67074f5
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: b2314d1e996ac7a4fbda72210b4aabbd915d282a
=======
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 75bf8bca5f9903b4f6e8fba693d61af1415d512f
>>>>>>> main
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

typedef uint8_t core_result_Result_____core_fmt_Error_tags;

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

<<<<<<< HEAD
typedef struct
    core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_6f_tags;

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_6f_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_1c(core_result_Result_6f self,
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

<<<<<<< HEAD
typedef struct
    core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
/**
A monomorphic instance of core.result.Result
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_7a_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_34(core_result_Result_7a self,
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

<<<<<<< HEAD
typedef struct
    core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_cd_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_e8(core_result_Result_cd self,
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
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1088
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_d4_8a(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#14}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_b6
with const generics
- SIZE= 1184
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_15
libcrux_ml_kem_types_from_b6_4c(uint8_t value[1184U]) {
  uint8_t uu____0[1184U];
  memcpy(uu____0, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_15 lit;
  memcpy(lit.value, uu____0, (size_t)1184U * sizeof(uint8_t));
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
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_17_c9(libcrux_ml_kem_types_MlKemPrivateKey_55 sk,
                                libcrux_ml_kem_types_MlKemPublicKey_15 pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk, .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#8}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_05
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_55
libcrux_ml_kem_types_from_05_a7(uint8_t value[2400U]) {
  uint8_t uu____0[2400U];
  memcpy(uu____0, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 lit;
  memcpy(lit.value, uu____0, (size_t)2400U * sizeof(uint8_t));
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
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_01
with const generics
- SIZE= 1088
*/
static inline libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types_from_01_f5(uint8_t value[1088U]) {
  uint8_t uu____0[1088U];
  memcpy(uu____0, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, uu____0, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#18}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_cb
with const generics
- SIZE= 1184
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_cb_f2(
    libcrux_ml_kem_types_MlKemPublicKey_15 *self) {
  return self->value;
}

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_2d2(
    Eurydice_slice slice, uint8_t ret[33U]) {
  uint8_t out[33U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, (size_t)0U,
          core_slice___Slice_T___len(slice, uint8_t, size_t), uint8_t,
          Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)33U * sizeof(uint8_t));
}

<<<<<<< HEAD
typedef struct
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_00_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_83(core_result_Result_00 self,
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
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_2d1(
    Eurydice_slice slice, uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, (size_t)0U,
          core_slice___Slice_T___len(slice, uint8_t, size_t), uint8_t,
          Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#1}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_00
with const generics
- SIZE= 1088
*/
static inline Eurydice_slice libcrux_ml_kem_types_as_ref_00_47(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1088U, self->value, uint8_t,
                                 Eurydice_slice);
}

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_2d0(
    Eurydice_slice slice, uint8_t ret[1120U]) {
  uint8_t out[1120U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, (size_t)0U,
          core_slice___Slice_T___len(slice, uint8_t, size_t), uint8_t,
          Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)1120U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_2d(
    Eurydice_slice slice, uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice2(
          uu____0, (size_t)0U,
          core_slice___Slice_T___len(slice, uint8_t, size_t), uint8_t,
          Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

<<<<<<< HEAD
typedef struct
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_c0_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_f9(core_result_Result_c0 self,
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

<<<<<<< HEAD
typedef struct
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError_s {
  core_result_Result_____core_fmt_Error_tags tag;
=======
/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_56_s {
  core_result_Result_6f_tags tag;
>>>>>>> main
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
static inline void core_result_unwrap_41_ac(core_result_Result_56 self,
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
