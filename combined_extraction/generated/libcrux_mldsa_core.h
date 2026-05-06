/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 377317d6b25702c46ffff072fa00a3e32095e46f
 * Eurydice: b227478b67c6a6e2ff611f978f10d6b7f26472ac
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: unset
 * Libcrux: d3ed1c47cd34e327523d0f5444286676b7f7abe1
 */


#ifndef libcrux_mldsa_core_H
#define libcrux_mldsa_core_H

#include "eurydice_glue.h"



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
static inline const
Eurydice_arr_96
*libcrux_ml_dsa_types_as_ref_c5_fa(const Eurydice_arr_96 *self)
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
Eurydice_arr_4a
*libcrux_ml_dsa_types_as_ref_7f_97(const Eurydice_arr_4a *self)
{
  return self;
}

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_VerificationError

*/
typedef struct Result_41_s
{
  Result_80_tags tag;
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
Eurydice_arr_d10
*libcrux_ml_dsa_types_as_ref_9b_09(const Eurydice_arr_d10 *self)
{
  return self;
}

/**
A monomorphic instance of core.result.Result
with types libcrux_ml_dsa_types_MLDSASignature_8f, libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_97_s
{
  Result_80_tags tag;
  union U {
    Eurydice_arr_96 case_Ok;
    libcrux_ml_dsa_types_SigningError case_Err;
  }
  val;
  KRML_UNION_CONSTRUCTOR(Result_97_s)
}
Result_97;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_ml_dsa_types_SigningError

*/
typedef struct Result_53_s
{
  Result_80_tags tag;
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
static inline Eurydice_arr_96 libcrux_ml_dsa_types_zero_c5_fa(void)
{
  return (Eurydice_arr_96{ { 0U } });
}

/**
A monomorphic instance of libcrux_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_ml_dsa_types_MLDSAKeyPair_06_s
{
  Eurydice_arr_d10 signing_key;
  Eurydice_arr_4a verification_key;
}
libcrux_ml_dsa_types_MLDSAKeyPair_06;

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
static inline Eurydice_arr_4a libcrux_ml_dsa_types_new_7f_97(Eurydice_arr_4a value)
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
static inline Eurydice_arr_d10 libcrux_ml_dsa_types_new_9b_09(Eurydice_arr_d10 value)
{
  return value;
}


#define libcrux_mldsa_core_H_DEFINED
#endif /* libcrux_mldsa_core_H */
