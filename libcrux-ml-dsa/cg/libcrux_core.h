/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 763350c6948d5594d3017ecb93273bc41c1a4e1d
 * Eurydice: 1182698fe56bc99a58f00403c79126bda24dda72
 * Karamel: 8ac6c2e18f936b6fdb788ae94367942016a60f8c
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 1a5298140c8be6bc97ac6652bac9844ff2ed06fb
 */

#ifndef __libcrux_core_H
#define __libcrux_core_H

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

static inline uint8_t
core_ops_bit___core__ops__bit__BitAnd_u8__u8__for___a__u8___46__bitand(
    uint8_t *x0, uint8_t x1);

static inline uint8_t
core_ops_bit___core__ops__bit__Shr_i32__u8__for___a__u8___792__shr(uint8_t *x0,
                                                                   int32_t x1);

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSASignature_8f_s {
  uint8_t value[3309U];
} libcrux_ml_dsa_types_MLDSASignature_8f;

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
    libcrux_ml_dsa_types_MLDSASignature_8f *self) {
  return self->value;
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
  union U {
    libcrux_ml_dsa_types_MLDSASignature_8f case_Ok;
    libcrux_ml_dsa_types_SigningError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_2e_s)
} Result_2e;

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

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_53_s {
  Result_a9_tags tag;
  libcrux_ml_dsa_types_SigningError f0;
} Result_53;

/**
 Init with zero
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASignature<SIZE>#4}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.zero_8f
with const generics
- SIZE= 3309
*/
static inline libcrux_ml_dsa_types_MLDSASignature_8f
libcrux_ml_dsa_types_zero_8f_fa(void) {
  libcrux_ml_dsa_types_MLDSASignature_8f lit;
  uint8_t repeat_expression[3309U] = {0U};
  memcpy(lit.value, repeat_expression, (size_t)3309U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSAKeyPair_06_s {
  libcrux_ml_dsa_types_MLDSASigningKey_22 signing_key;
  libcrux_ml_dsa_types_MLDSAVerificationKey_ea verification_key;
} libcrux_ml_dsa_types_MLDSAKeyPair_06;

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
A monomorphic instance of core.option.Option
with types uint8_t[11size_t]

*/
typedef struct Option_30_s {
  Option_d8_tags tag;
  uint8_t f0[11U];
} Option_30;

typedef struct Eurydice_slice_uint8_t_200size_t__x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_200size_t__x2;

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

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

#define __libcrux_core_H_DEFINED
#endif
