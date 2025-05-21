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

#ifndef __libcrux_mlkem_core_H
#define __libcrux_mlkem_core_H

#include "eurydice_glue.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define Ok 0
#define Err 1

typedef uint8_t Result_a9_tags;

static inline uint16_t core_num__u16_7__wrapping_add(uint16_t x0, uint16_t x1);

#define CORE_NUM__U32_8__BITS (32U)

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline uint64_t core_num__u64_9__rotate_left(uint64_t x0, uint32_t x1);

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

#define LIBCRUX_ML_KEM_CONSTANTS_G_DIGEST_SIZE ((size_t)64U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
static inline size_t libcrux_ml_kem_constants_ranked_bytes_per_ring_element(
    size_t rank) {
  return rank * LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U;
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t
libcrux_secrets_int_public_integers_classify_57_90(uint8_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int16_t

*/
static KRML_MUSTINLINE int16_t
libcrux_secrets_int_public_integers_declassify_73_39(int16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_d2(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t

*/
static KRML_MUSTINLINE int16_t
libcrux_secrets_int_public_integers_classify_57_39(int16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t
libcrux_secrets_int_public_integers_declassify_73_90(uint8_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u8)}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_84(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_73_90(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int32_t

*/
static KRML_MUSTINLINE int32_t
libcrux_secrets_int_public_integers_classify_57_a8(int32_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_d2(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int32_t

*/
static KRML_MUSTINLINE int32_t
libcrux_secrets_int_public_integers_declassify_73_a8(int32_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i32)#6}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_98(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_73_a8(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_declassify_73_df(uint32_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_41(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_57_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_73_df(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t
libcrux_secrets_int_public_integers_classify_57_de(uint16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_d2(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t
libcrux_secrets_int_public_integers_declassify_73_de(uint16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_e9(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_73_de(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_classify_57_49(uint64_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_e9(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_73_de(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_classify_57_df(uint32_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_declassify_73_49(uint64_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u64)#3}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_0b(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_57_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_73_49(self));
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_41(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_73_df(self));
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_d2(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      libcrux_secrets_int_public_integers_declassify_73_39(self));
}

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  uint8_t fst[1152U];
  uint8_t snd[1184U];
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

/**
A monomorphic instance of core.result.Result
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
typedef struct Result_b2_s {
  Result_a9_tags tag;
  union U {
    uint8_t case_Ok[24U];
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_b2_s)
} Result_b2;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_70(Result_b2 self, uint8_t ret[24U]) {
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
typedef struct Result_e1_s {
  Result_a9_tags tag;
  union U {
    uint8_t case_Ok[20U];
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_e1_s)
} Result_e1;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_20(Result_e1 self, uint8_t ret[20U]) {
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

typedef struct Eurydice_slice_uint8_t_200size_t__x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_200size_t__x2;

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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_9e(
    Eurydice_slice slice, uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_d9_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey_d9;

/**
This function found in impl {(core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#7}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_24
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_types_default_24_28(void) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 lit;
  uint8_t repeat_expression[2400U] = {0U};
  memcpy(lit.value, repeat_expression, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_30_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_30;

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 1184
*/
static inline libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_types_from_5f_d0(uint8_t value[1184U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1184U];
  memcpy(copy_of_value, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_30 lit;
  memcpy(lit.value, copy_of_value, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_ml_kem_types_MlKemPublicKey_30 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

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
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_3a_74(libcrux_ml_kem_types_MlKemPrivateKey_d9 sk,
                                libcrux_ml_kem_types_MlKemPublicKey_30 pk) {
  return (libcrux_ml_kem_mlkem768_MlKem768KeyPair{sk, pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 2400
*/
static inline libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_types_from_9a_28(uint8_t value[2400U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2400U];
  memcpy(copy_of_value, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 lit;
  memcpy(lit.value, copy_of_value, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct Result_fb_s {
  Result_a9_tags tag;
  union U {
    uint8_t case_Ok[32U];
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_fb_s)
} Result_fb;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_b3(Result_fb self, uint8_t ret[32U]) {
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

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s {
  uint8_t value[1088U];
} libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_c2_s {
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
} tuple_c2;

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 1088
*/
static inline libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types_from_00_80(uint8_t value[1088U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1088U];
  memcpy(copy_of_value, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, copy_of_value, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 1184
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_fd_d0(
    libcrux_ml_kem_types_MlKemPublicKey_30 *self) {
  return self->value;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1088
*/
static inline uint8_t *libcrux_ml_kem_types_as_slice_d4_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
static KRML_MUSTINLINE uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(
    uint8_t (*prf_inputs)[33U], uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs[i0][32U] = domain_separator;
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_c8(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_b6(
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
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 1088
*/
static inline Eurydice_slice libcrux_ml_kem_types_as_ref_43_80(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_15(
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
static KRML_MUSTINLINE void libcrux_ml_kem_utils_into_padded_array_24(
    Eurydice_slice slice, uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

typedef struct Eurydice_slice_uint8_t_x4_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
  Eurydice_slice thd;
  Eurydice_slice f3;
} Eurydice_slice_uint8_t_x4;

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

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
static inline Eurydice_slice_uint8_t_x4
libcrux_ml_kem_types_unpack_private_key_b4(Eurydice_slice private_key) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  return (Eurydice_slice_uint8_t_x4{ind_cpa_secret_key, ind_cpa_public_key,
                                    ind_cpa_public_key_hash,
                                    implicit_rejection_value});
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[24size_t]

*/
static KRML_MUSTINLINE void
libcrux_secrets_int_public_integers_declassify_73_d2(uint8_t self[24U],
                                                     uint8_t ret[24U]) {
  memcpy(ret, self, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[20size_t]

*/
static KRML_MUSTINLINE void
libcrux_secrets_int_public_integers_declassify_73_57(uint8_t self[20U],
                                                     uint8_t ret[20U]) {
  memcpy(ret, self, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[8size_t]

*/
static KRML_MUSTINLINE void
libcrux_secrets_int_public_integers_declassify_73_76(uint8_t self[8U],
                                                     uint8_t ret[8U]) {
  memcpy(ret, self, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[2size_t]

*/
static KRML_MUSTINLINE void
libcrux_secrets_int_public_integers_declassify_73_d4(uint8_t self[2U],
                                                     uint8_t ret[2U]) {
  memcpy(ret, self, (size_t)2U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t[16size_t]

*/
static KRML_MUSTINLINE void libcrux_secrets_int_public_integers_classify_57_46(
    int16_t self[16U], int16_t ret[16U]) {
  memcpy(ret, self, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice uint8_t

*/
static KRML_MUSTINLINE Eurydice_slice *
libcrux_secrets_int_public_integers_classify_ref_b8_ba(Eurydice_slice *self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice int16_t

*/
static KRML_MUSTINLINE Eurydice_slice *
libcrux_secrets_int_public_integers_classify_ref_b8_03(Eurydice_slice *self) {
  return self;
}

/**
A monomorphic instance of core.result.Result
with types int16_t[16size_t], core_array_TryFromSliceError

*/
typedef struct Result_0a_s {
  Result_a9_tags tag;
  union U {
    int16_t case_Ok[16U];
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_0a_s)
} Result_0a;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_00(Result_0a self, int16_t ret[16U]) {
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
typedef struct Result_15_s {
  Result_a9_tags tag;
  union U {
    uint8_t case_Ok[8U];
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_15_s)
} Result_15;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_68(Result_15 self, uint8_t ret[8U]) {
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

typedef struct Eurydice_slice_uint8_t_1size_t__x2_s {
  Eurydice_slice fst[1U];
  Eurydice_slice snd[1U];
} Eurydice_slice_uint8_t_1size_t__x2;

#define __libcrux_mlkem_core_H_DEFINED
#endif
