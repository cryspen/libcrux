/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 65c45918a38d1b3e2155d3d69e9831b670d0a09f
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: baec61db14d5132ae8eb4bd7a288638b7f2f1db8
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 6a8770c9d9d51b553169e0f2cc8cfd808fc7caa6
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

#define None 0
#define Some 1

typedef uint8_t Option_b3_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct Option_b3_s {
  Option_b3_tags tag;
  size_t f0;
} Option_b3;

#define Ok 0
#define Err 1

typedef uint8_t Result_86_tags;

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

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct Result_6f_s {
  Result_86_tags tag;
  union {
    uint8_t case_Ok[24U];
    TryFromSliceError case_Err;
  } val;
} Result_6f;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_76(Result_6f self, uint8_t ret[24U]) {
  if (self.tag == Ok) {
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
typedef struct Result_7a_s {
  Result_86_tags tag;
  union {
    uint8_t case_Ok[20U];
    TryFromSliceError case_Err;
  } val;
} Result_7a;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_ea(Result_7a self, uint8_t ret[20U]) {
  if (self.tag == Ok) {
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
typedef struct Result_cd_s {
  Result_86_tags tag;
  union {
    uint8_t case_Ok[10U];
    TryFromSliceError case_Err;
  } val;
} Result_cd;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_07(Result_cd self, uint8_t ret[10U]) {
  if (self.tag == Ok) {
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
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_423(
    Eurydice_slice slice, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_07
with const generics
- SIZE= 1088
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_07_46(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_15_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_15;

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#17}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_40
with const generics
- SIZE= 1184
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_15
libcrux_ml_kem_types_from_40_cb(uint8_t value[1184U]) {
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
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_17_dc(libcrux_ml_kem_types_MlKemPrivateKey_55 sk,
                                libcrux_ml_kem_types_MlKemPublicKey_15 pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk, .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#10}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_88
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_55
libcrux_ml_kem_types_from_88_58(uint8_t value[2400U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2400U];
  memcpy(copy_of_value, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_55 lit;
  memcpy(lit.value, copy_of_value, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct Result_00_s {
  Result_86_tags tag;
  union {
    uint8_t case_Ok[32U];
    TryFromSliceError case_Err;
  } val;
} Result_00;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_33(Result_00 self, uint8_t ret[32U]) {
  if (self.tag == Ok) {
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
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#3}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fc
with const generics
- SIZE= 1088
*/
static inline libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types_from_fc_89(uint8_t value[1088U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1088U];
  memcpy(copy_of_value, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, copy_of_value, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

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
static inline uint8_t *libcrux_ml_kem_types_as_slice_ba_c1(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_422(
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
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_421(
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
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#2}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_fd
with const generics
- SIZE= 1088
*/
static inline Eurydice_slice libcrux_ml_kem_types_as_ref_fd_89(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_420(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_42(
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
typedef struct Result_c0_s {
  Result_86_tags tag;
  union {
    int16_t case_Ok[16U];
    TryFromSliceError case_Err;
  } val;
} Result_c0;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_30(Result_c0 self, int16_t ret[16U]) {
  if (self.tag == Ok) {
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
typedef struct Result_56_s {
  Result_86_tags tag;
  union {
    uint8_t case_Ok[8U];
    TryFromSliceError case_Err;
  } val;
} Result_56;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_0e(Result_56 self, uint8_t ret[8U]) {
  if (self.tag == Ok) {
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
