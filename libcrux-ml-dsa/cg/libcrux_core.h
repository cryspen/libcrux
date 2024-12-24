/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: db4e045d4597d06d854ce7a2c10e8dcfda6ecd25
 * Eurydice: 83ab5654d49df0603797bf510475d52d67ca24d8
 * Karamel: 3823e3d82fa0b271d799b61c59ffb4742ddc1e65
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: eb80bb89b0a5fc54d9c40357cdfb9b21cb9ff941
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
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

static inline uint8_t Eurydice_bitand_pv_u8(uint8_t *x, uint8_t y);

static inline uint8_t Eurydice_shr_pv_u8(uint8_t *x, int32_t y);

#define Ok 0
#define Err 1

typedef uint8_t Result_a9_tags;

#define None 0
#define Some 1

typedef uint8_t Option_d8_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct Option_08_s {
  Option_d8_tags tag;
  size_t f0;
} Option_08;

static inline uint32_t core_num__i32_2__count_ones(int32_t x0);

static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t x0[8U]);

static inline void core_num__u64_9__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
typedef struct Result_9d_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[10U];
    TryFromSliceError case_Err;
  } val;
} Result_9d;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_ce(Result_9d self, uint8_t ret[10U]) {
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

/**
A monomorphic instance of core.result.Result
with types uint8_t[13size_t], core_array_TryFromSliceError

*/
typedef struct Result_b0_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[13U];
    TryFromSliceError case_Err;
  } val;
} Result_b0;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[13size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_23(Result_b0 self, uint8_t ret[13U]) {
  if (self.tag == Ok) {
    uint8_t f0[13U];
    memcpy(f0, self.val.case_Ok, (size_t)13U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)13U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

typedef struct libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature_s {
  uint8_t value[3309U];
} libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASignature<SIZE>#4}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.as_ref_8f
with const generics
- SIZE= 3309
*/
static inline uint8_t *libcrux_ml_dsa_types_as_ref_8f_fa(
    libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature *self) {
  return self->value;
}

#define libcrux_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError 1
#define libcrux_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError 2
#define libcrux_ml_dsa_types_VerificationError_VerificationContextTooLongError 3

typedef uint8_t libcrux_ml_dsa_types_VerificationError;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_VerificationError

*/
typedef struct Result_41_s {
  Result_a9_tags tag;
  libcrux_ml_dsa_types_VerificationError f0;
} Result_41;

/**
A monomorphic instance of core.result.Result
with types uint8_t[48size_t], core_array_TryFromSliceError

*/
typedef struct Result_ae_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[48U];
    TryFromSliceError case_Err;
  } val;
} Result_ae;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[48size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_28(Result_ae self, uint8_t ret[48U]) {
  if (self.tag == Ok) {
    uint8_t f0[48U];
    memcpy(f0, self.val.case_Ok, (size_t)48U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)48U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSAVerificationKey
with const generics
- $1952size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSAVerificationKey_ea_s {
  uint8_t value[1952U];
} libcrux_ml_dsa_types_MLDSAVerificationKey_ea;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_ml_dsa::types::MLDSAVerificationKey<SIZE>#2}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.as_ref_66
with const generics
- SIZE= 1952
*/
static inline uint8_t *libcrux_ml_dsa_types_as_ref_66_97(
    libcrux_ml_dsa_types_MLDSAVerificationKey_ea *self) {
  return self->value;
}

/**
A monomorphic instance of core.option.Option
with types int32_t[256size_t][6size_t]

*/
typedef struct Option_f0_s {
  Option_d8_tags tag;
  int32_t f0[6U][256U];
} Option_f0;

/**
A monomorphic instance of core.option.Option
with types uint8_t[48size_t]

*/
typedef struct Option_67_s {
  Option_d8_tags tag;
  uint8_t f0[48U];
} Option_67;

#define libcrux_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_ml_dsa_types_SigningError;

/**
A monomorphic instance of core.result.Result
with types libcrux_ml_dsa_types_MLDSASignature[[$3309size_t]],
libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_2e_s {
  Result_a9_tags tag;
  union {
    libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature case_Ok;
    libcrux_ml_dsa_types_SigningError case_Err;
  } val;
} Result_2e;

/**
 Build
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASignature<SIZE>#4}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.new_8f
with const generics
- SIZE= 3309
*/
static inline libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature
libcrux_ml_dsa_types_new_8f_fa(uint8_t value[3309U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[3309U];
  memcpy(copy_of_value, value, (size_t)3309U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature lit;
  memcpy(lit.value, copy_of_value, (size_t)3309U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[64size_t], core_array_TryFromSliceError

*/
typedef struct Result_f2_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[64U];
    TryFromSliceError case_Err;
  } val;
} Result_f2;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[64size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_4b(Result_f2 self, uint8_t ret[64U]) {
  if (self.tag == Ok) {
    uint8_t f0[64U];
    memcpy(f0, self.val.case_Ok, (size_t)64U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)64U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct Result_fb_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[32U];
    TryFromSliceError case_Err;
  } val;
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

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSASigningKey
with const generics
- $4032size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSASigningKey_22_s {
  uint8_t value[4032U];
} libcrux_ml_dsa_types_MLDSASigningKey_22;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.as_ref_9b
with const generics
- SIZE= 4032
*/
static inline uint8_t *libcrux_ml_dsa_types_as_ref_9b_09(
    libcrux_ml_dsa_types_MLDSASigningKey_22 *self) {
  return self->value;
}

/**
 Build
*/
/**
This function found in impl
{libcrux_ml_dsa::types::MLDSAVerificationKey<SIZE>#2}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.new_66
with const generics
- SIZE= 1952
*/
static inline libcrux_ml_dsa_types_MLDSAVerificationKey_ea
libcrux_ml_dsa_types_new_66_97(uint8_t value[1952U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1952U];
  memcpy(copy_of_value, value, (size_t)1952U * sizeof(uint8_t));
  libcrux_ml_dsa_types_MLDSAVerificationKey_ea lit;
  memcpy(lit.value, copy_of_value, (size_t)1952U * sizeof(uint8_t));
  return lit;
}

/**
 Build
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.new_9b
with const generics
- SIZE= 4032
*/
static inline libcrux_ml_dsa_types_MLDSASigningKey_22
libcrux_ml_dsa_types_new_9b_09(uint8_t value[4032U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[4032U];
  memcpy(copy_of_value, value, (size_t)4032U * sizeof(uint8_t));
  libcrux_ml_dsa_types_MLDSASigningKey_22 lit;
  memcpy(lit.value, copy_of_value, (size_t)4032U * sizeof(uint8_t));
  return lit;
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_dsa.utils.into_padded_array
with const generics
- LEN= 66
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_utils_into_padded_array_20(
    Eurydice_slice slice, uint8_t ret[66U]) {
  uint8_t out[66U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)66U * sizeof(uint8_t));
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_dsa.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_utils_into_padded_array_b6(
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
A monomorphic instance of core.result.Result
with types int32_t[8size_t], core_array_TryFromSliceError

*/
typedef struct Result_6c_s {
  Result_a9_tags tag;
  union {
    int32_t case_Ok[8U];
    TryFromSliceError case_Err;
  } val;
} Result_6c;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int32_t[8size_t], core_array_TryFromSliceError

*/
static inline void unwrap_26_55(Result_6c self, int32_t ret[8U]) {
  if (self.tag == Ok) {
    int32_t f0[8U];
    memcpy(f0, self.val.case_Ok, (size_t)8U * sizeof(int32_t));
    memcpy(ret, f0, (size_t)8U * sizeof(int32_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.option.Option
with types uint8_t[11size_t]

*/
typedef struct Option_30_s {
  Option_d8_tags tag;
  uint8_t f0[11U];
} Option_30;

typedef struct libcrux_ml_dsa_ml_dsa_65_MLDSA65KeyPair_s {
  libcrux_ml_dsa_types_MLDSASigningKey_22 signing_key;
  libcrux_ml_dsa_types_MLDSAVerificationKey_ea verification_key;
} libcrux_ml_dsa_ml_dsa_65_MLDSA65KeyPair;

typedef struct Eurydice_slice_uint8_t_4size_t__x2_s {
  Eurydice_slice fst[4U];
  Eurydice_slice snd[4U];
} Eurydice_slice_uint8_t_4size_t__x2;

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct Result_15_s {
  Result_a9_tags tag;
  union {
    uint8_t case_Ok[8U];
    TryFromSliceError case_Err;
  } val;
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
