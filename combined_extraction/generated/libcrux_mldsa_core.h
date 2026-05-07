/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: db1b72c6b2fdb686fe0c00e95e3415978d3ce1f9
 * Eurydice: 01a00d0c9df19a58c2b8513f049354b4719d5922
 * Karamel: 2fe560bbae17fe8a855b0dcf462db18ec37edc02
 * F*: 9c3cf2e2f27cefc577e423f272e5c33f8c11f2bc
 * Libcrux: e75f8edd9f168ae08eeea8aaf1445bc6111c2356
 */


#ifndef libcrux_mldsa_core_H
#define libcrux_mldsa_core_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

#define libcrux_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError 1
#define libcrux_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError 2
#define libcrux_ml_dsa_types_VerificationError_VerificationContextTooLongError 3

typedef uint8_t libcrux_ml_dsa_types_VerificationError;

#define libcrux_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_ml_dsa_types_SigningError;

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef Eurydice_arr_0c libcrux_ml_dsa_types_MLDSASignature_aa;

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
static inline const
Eurydice_arr_0c
*libcrux_ml_dsa_types_as_ref_c5_5c(const Eurydice_arr_0c *self)
{
  return self;
}

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
static inline const
Eurydice_arr_29
*libcrux_ml_dsa_types_as_ref_7f_a2(const Eurydice_arr_29 *self)
{
  return self;
}

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_VerificationError

*/
typedef struct Result_41_s
{
  Result_57_tags tag;
  libcrux_ml_dsa_types_VerificationError f0;
}
Result_41;

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
static inline const
Eurydice_arr_24
*libcrux_ml_dsa_types_as_ref_9b_e5(const Eurydice_arr_24 *self)
{
  return self;
}

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_53_s
{
  Result_57_tags tag;
  libcrux_ml_dsa_types_SigningError f0;
}
Result_53;

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
static inline Eurydice_arr_0c libcrux_ml_dsa_types_zero_c5_5c(void)
{
  return (KRML_CLITERAL(Eurydice_arr_0c){ .data = { 0U } });
}

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSAKeyPair_d5_s
{
  Eurydice_arr_24 signing_key;
  Eurydice_arr_29 verification_key;
}
libcrux_ml_dsa_types_MLDSAKeyPair_d5;

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
static inline Eurydice_arr_29 libcrux_ml_dsa_types_new_7f_a2(Eurydice_arr_29 value)
{
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
static inline Eurydice_arr_24 libcrux_ml_dsa_types_new_9b_e5(Eurydice_arr_24 value)
{
  return value;
}

#if defined(__cplusplus)
}
#endif

#define libcrux_mldsa_core_H_DEFINED
#endif /* libcrux_mldsa_core_H */
