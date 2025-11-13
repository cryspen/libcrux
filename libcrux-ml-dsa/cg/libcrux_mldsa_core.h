/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: aa8de1a51675fbf6b65135d38d7e3986cadc626f
 * Eurydice: 5dbfcfb3f8f694a4b23d120d18400692e22050d5
 * Karamel: 46bbe26187c3d295b0d78152b6ea447aaf32dac8
 * F*: unset
 * Libcrux: 2aefcf58f546cc3710114f9f794ae3f3bb31d88f
 */

#ifndef libcrux_mldsa_core_H
#define libcrux_mldsa_core_H

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"

#define None 0
#define Some 1

typedef uint8_t Option_08_tags;

static inline uint32_t core_num__i32__count_ones(int32_t x0);

#define CORE_NUM__U32__MAX (~0U)

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_arr_c4 x0);

static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1);

static inline Eurydice_arr_c4 core_num__u64__to_le_bytes(uint64_t x0);

static inline uint8_t
core_ops_bit__core__ops__bit__BitAnd_u8__u8__for__0__u8___bitand(uint8_t *x0,
                                                                 uint8_t x1);

static inline uint8_t
core_ops_bit__core__ops__bit__Shr_i32__u8__for__0__u8___shr(uint8_t *x0,
                                                            int32_t x1);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define libcrux_ml_dsa_constants_Eta_Two 2
#define libcrux_ml_dsa_constants_Eta_Four 4

typedef uint8_t libcrux_ml_dsa_constants_Eta;

#define LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T ((size_t)13U)

#define LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH \
  ((size_t)23U)

#define LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T         \
  (LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - \
   LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T)

#define LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN ((size_t)255U)

#define LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS ((int32_t)8380417)

#define LIBCRUX_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN ((size_t)814U)

#define LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE \
  (LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T *     \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE \
  (LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T *     \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE ((size_t)32U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE ((size_t)32U)

static inline int32_t libcrux_ml_dsa_constants_beta(
    size_t ones_in_verifier_challenge, libcrux_ml_dsa_constants_Eta eta) {
  size_t eta_val;
  switch (eta) {
    case libcrux_ml_dsa_constants_Eta_Two: {
      eta_val = (size_t)2U;
      break;
    }
    case libcrux_ml_dsa_constants_Eta_Four: {
      eta_val = (size_t)4U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (int32_t)(ones_in_verifier_challenge * eta_val);
}

static inline size_t libcrux_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient) {
  return bits_per_commitment_coefficient *
         LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a) {
  return libcrux_ml_dsa_constants_commitment_ring_element_size(
             bits_per_commitment_coefficient) *
         rows_in_a;
}

static inline size_t libcrux_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient) {
  return bits_per_error_coefficient *
         LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient) {
  return bits_per_gamma1_coefficient *
         LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

static inline size_t libcrux_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient) {
  return commitment_hash_size +
         columns_in_a * libcrux_ml_dsa_constants_gamma1_ring_element_size(
                            bits_per_gamma1_coefficient) +
         max_ones_in_hint + rows_in_a;
}

static inline size_t libcrux_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size) {
  return LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE +
         LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH +
         (rows_in_a + columns_in_a) * error_ring_element_size +
         rows_in_a * LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
}

static inline size_t libcrux_ml_dsa_constants_verification_key_size(
    size_t rows_in_a) {
  return LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * rows_in_a *
             (LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -
              LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) /
             (size_t)8U;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_6d_s {
  uint8_t data[24U];
} Eurydice_arr_6d;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 24
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3610(
    Eurydice_arr_6d *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_88_s {
  uint8_t data[16U];
} Eurydice_arr_88;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 16
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_369(
    Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $19size_t
*/
typedef struct Eurydice_arr_910_s {
  uint8_t data[19U];
} Eurydice_arr_910;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 19
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_368(
    Eurydice_arr_910 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 16
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_46(
    Eurydice_arr_88 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$16size_t]]
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_db_s {
  Eurydice_arr_88 data[16U];
} Eurydice_arr_db;

typedef struct libcrux_sha3_Sha3_256Digest_s {
  uint8_t data[32U];
} libcrux_sha3_Sha3_256Digest;

/**
A monomorphic instance of Eurydice.array_to_subslice_to
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 32
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_to_6e(
    libcrux_sha3_Sha3_256Digest *a, size_t r) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3309size_t
*/
typedef struct Eurydice_arr_96_s {
  uint8_t data[3309U];
} Eurydice_arr_96;

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef Eurydice_arr_96 libcrux_ml_dsa_types_MLDSASignature_8f;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.as_ref_c5
with const generics
- SIZE= 3309
*/
static inline Eurydice_arr_96 *libcrux_ml_dsa_types_as_ref_c5_fa(
    Eurydice_arr_96 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1952size_t
*/
typedef struct Eurydice_arr_4a_s {
  uint8_t data[1952U];
} Eurydice_arr_4a;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.as_ref_7f
with const generics
- SIZE= 1952
*/
static inline Eurydice_arr_4a *libcrux_ml_dsa_types_as_ref_7f_97(
    Eurydice_arr_4a *self) {
  return self;
}

#define libcrux_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError 1
#define libcrux_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError 2
#define libcrux_ml_dsa_types_VerificationError_VerificationContextTooLongError 3

typedef uint8_t libcrux_ml_dsa_types_VerificationError;

#define Ok 0
#define Err 1

typedef uint8_t Result_41_tags;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_VerificationError

*/
typedef struct Result_41_s {
  Result_41_tags tag;
  libcrux_ml_dsa_types_VerificationError f0;
} Result_41;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4032size_t
*/
typedef struct Eurydice_arr_d10_s {
  uint8_t data[4032U];
} Eurydice_arr_d10;

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
static inline Eurydice_arr_d10 *libcrux_ml_dsa_types_as_ref_9b_09(
    Eurydice_arr_d10 *self) {
  return self;
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
  Result_41_tags tag;
  union U {
    Eurydice_arr_96 case_Ok;
    libcrux_ml_dsa_types_SigningError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_2e_s)
} Result_2e;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_53_s {
  Result_41_tags tag;
  libcrux_ml_dsa_types_SigningError f0;
} Result_53;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 3309
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_ee0(
    Eurydice_arr_96 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3309U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_c3_s {
  int32_t data[256U];
} Eurydice_arr_c3;

/**
A monomorphic instance of Eurydice.dst_ref
with types Eurydice_arr int32_t[[$256size_t]], size_t

*/
typedef struct Eurydice_dst_ref_59_s {
  Eurydice_arr_c3 *ptr;
  size_t meta;
} Eurydice_dst_ref_59;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- $6size_t
*/
typedef struct Eurydice_arr_e6_s {
  Eurydice_arr_c3 data[6U];
} Eurydice_arr_e6;

/**
A monomorphic instance of Eurydice.array_to_slice
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
static inline Eurydice_dst_ref_59 Eurydice_array_to_slice_6d(
    Eurydice_arr_e6 *a) {
  Eurydice_dst_ref_59 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.dst_ref
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_fc_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_fc;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_subslice_7f0(
    Eurydice_arr_c3 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_fc{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $768size_t
*/
typedef struct Eurydice_arr_56_s {
  uint8_t data[768U];
} Eurydice_arr_56;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 768
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_ee(
    Eurydice_arr_56 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)768U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $640size_t
*/
typedef struct Eurydice_arr_c30_s {
  uint8_t data[640U];
} Eurydice_arr_c30;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 640
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_7d0(
    Eurydice_arr_c30 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)640U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $576size_t
*/
typedef struct Eurydice_arr_5f_s {
  uint8_t data[576U];
} Eurydice_arr_5f;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 576
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_fa(
    Eurydice_arr_5f *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)576U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $11size_t
*/
typedef struct Eurydice_arr_cb_s {
  uint8_t data[11U];
} Eurydice_arr_cb;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 11
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_da(
    Eurydice_arr_cb *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_f1_s {
  uint8_t data[1U];
} Eurydice_arr_f1;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_07(
    Eurydice_arr_f1 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
 Init with zero
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.zero_c5
with const generics
- SIZE= 3309
*/
static inline Eurydice_arr_96 libcrux_ml_dsa_types_zero_c5_fa(void) {
  return (Eurydice_arr_96{{0U}});
}

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSAKeyPair_06_s {
  Eurydice_arr_d10 signing_key;
  Eurydice_arr_4a verification_key;
} libcrux_ml_dsa_types_MLDSAKeyPair_06;

/**
 Build
*/
/**
This function found in impl {libcrux_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_dsa.types.new_7f
with const generics
- SIZE= 1952
*/
static inline Eurydice_arr_4a libcrux_ml_dsa_types_new_7f_97(
    Eurydice_arr_4a value) {
  return value;
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
static inline Eurydice_arr_d10 libcrux_ml_dsa_types_new_9b_09(
    Eurydice_arr_d10 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1952
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_5b(
    Eurydice_arr_4a *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1952U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 4032
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_ef(
    Eurydice_arr_d10 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4032U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $263size_t
*/
typedef struct Eurydice_arr_13_s {
  int32_t data[263U];
} Eurydice_arr_13;

/**
A monomorphic instance of Eurydice.dst_ref
with types Eurydice_arr int32_t[[$263size_t]], size_t

*/
typedef struct Eurydice_dst_ref_2c_s {
  Eurydice_arr_13 *ptr;
  size_t meta;
} Eurydice_dst_ref_2c;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int32_t[[$263size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_46_s {
  Eurydice_arr_13 data[4U];
} Eurydice_arr_46;

/**
A monomorphic instance of Eurydice.array_to_slice
with types Eurydice_arr int32_t[[$263size_t]]
with const generics
- N= 4
*/
static inline Eurydice_dst_ref_2c Eurydice_array_to_slice_f6(
    Eurydice_arr_46 *a) {
  Eurydice_dst_ref_2c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $34size_t
*/
typedef struct Eurydice_arr_48_s {
  uint8_t data[34U];
} Eurydice_arr_48;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 34
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_8d(
    Eurydice_arr_48 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)34U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types int32_t
with const generics
- N= 263
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_slice_200(
    Eurydice_arr_13 *a) {
  Eurydice_dst_ref_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)263U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from
with types int32_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_subslice_from_96(
    Eurydice_arr_13 *a, size_t r) {
  return (Eurydice_dst_ref_fc{a->data + r, (size_t)263U - r});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $66size_t
*/
typedef struct Eurydice_arr_a2_s {
  uint8_t data[66U];
} Eurydice_arr_a2;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 66
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_39(
    Eurydice_arr_a2 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)66U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_d1_s {
  uint8_t data[128U];
} Eurydice_arr_d1;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 128
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_18(
    Eurydice_arr_d1 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 2
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_26(
    Eurydice_arr_8b *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_d4_s {
  int32_t data[8U];
} Eurydice_arr_d4;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_subslice_7f(
    Eurydice_arr_d4 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_fc{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
static inline Eurydice_dst_ref_fc Eurydice_slice_subslice_46(
    Eurydice_dst_ref_fc s, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_fc{s.ptr + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types int32_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_slice_a7(
    Eurydice_arr_d4 *a) {
  Eurydice_dst_ref_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types int32_t
with const generics
- N= 256
*/
static inline Eurydice_dst_ref_fc Eurydice_array_to_slice_20(
    Eurydice_arr_c3 *a) {
  Eurydice_dst_ref_fc lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_367(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 66
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_366(
    Eurydice_arr_a2 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $840size_t
*/
typedef struct Eurydice_arr_12_s {
  uint8_t data[840U];
} Eurydice_arr_12;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 840
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_a8(
    Eurydice_arr_12 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)840U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_3d_s {
  uint8_t data[136U];
} Eurydice_arr_3d;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$136size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_91_s {
  Eurydice_arr_3d data[4U];
} Eurydice_arr_91;

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_c0_s {
  __m256i data[5U];
} Eurydice_arr_c0;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $168size_t
*/
typedef struct Eurydice_arr_27_s {
  uint8_t data[168U];
} Eurydice_arr_27;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_a6_s {
  Eurydice_arr_27 data[4U];
} Eurydice_arr_a6;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_dst_ref uint8_t size_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_66_s {
  Eurydice_dst_ref_87 data[4U];
} Eurydice_arr_66;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_365(
    libcrux_sha3_Sha3_256Digest *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_x86___m256i
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_05_s {
  __m256i data[25U];
} Eurydice_arr_05;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_75_s {
  Eurydice_arr_27 data[1U];
} Eurydice_arr_75;

typedef struct libcrux_sha3_Sha3_512Digest_s {
  uint8_t data[64U];
} libcrux_sha3_Sha3_512Digest;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 64
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_d8(
    libcrux_sha3_Sha3_512Digest *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

typedef struct libcrux_sha3_Sha3_384Digest_s {
  uint8_t data[48U];
} libcrux_sha3_Sha3_384Digest;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 48
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_95(
    libcrux_sha3_Sha3_384Digest *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 32
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_6e(
    libcrux_sha3_Sha3_256Digest *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

typedef struct libcrux_sha3_Sha3_224Digest_s {
  uint8_t data[28U];
} libcrux_sha3_Sha3_224Digest;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 28
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_c0(
    libcrux_sha3_Sha3_224Digest *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)28U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $72size_t
*/
typedef struct Eurydice_arr_a0_s {
  uint8_t data[72U];
} Eurydice_arr_a0;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 72
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_7d(
    Eurydice_arr_a0 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)72U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 72
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_364(
    Eurydice_arr_a0 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $104size_t
*/
typedef struct Eurydice_arr_18_s {
  uint8_t data[104U];
} Eurydice_arr_18;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 104
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_9c(
    Eurydice_arr_18 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)104U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 104
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_363(
    Eurydice_arr_18 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $144size_t
*/
typedef struct Eurydice_arr_a8_s {
  uint8_t data[144U];
} Eurydice_arr_a8;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 144
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_d1(
    Eurydice_arr_a8 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)144U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 144
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_362(
    Eurydice_arr_a8 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
static inline Eurydice_dst_ref_87 Eurydice_slice_subslice_from_6b(
    Eurydice_dst_ref_87 s, size_t r) {
  return (Eurydice_dst_ref_87{s.ptr + r, s.meta - r});
}

/**
A monomorphic instance of Eurydice.slice_subslice_to
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
static inline Eurydice_dst_ref_87 Eurydice_slice_subslice_to_c6(
    Eurydice_dst_ref_87 s, size_t r) {
  return (Eurydice_dst_ref_87{s.ptr, r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_from_8c(
    Eurydice_arr_3d *a, size_t r) {
  return (Eurydice_dst_ref_87{a->data + r, (size_t)136U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_361(
    Eurydice_arr_c4 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_41(
    Eurydice_arr_c4 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 136
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_d4(
    Eurydice_arr_3d *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)136U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_360(
    Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_a5_s {
  uint64_t data[5U];
} Eurydice_arr_a5;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_dst_ref uint8_t size_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_e2_s {
  Eurydice_dst_ref_87 data[1U];
} Eurydice_arr_e2;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 168
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_7b(
    Eurydice_arr_27 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)168U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
static inline Eurydice_dst_ref_87 Eurydice_slice_subslice_7e(
    Eurydice_dst_ref_87 s, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{s.ptr + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_36(
    Eurydice_arr_27 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_a7_s {
  uint64_t data[24U];
} Eurydice_arr_a7;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$136size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_c40_s {
  Eurydice_arr_3d data[1U];
} Eurydice_arr_c40;

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_26_s {
  uint64_t data[25U];
} Eurydice_arr_26;

#define libcrux_mldsa_core_H_DEFINED
#endif /* libcrux_mldsa_core_H */
