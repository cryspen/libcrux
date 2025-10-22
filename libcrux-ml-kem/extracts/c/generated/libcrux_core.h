/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 2381cbc416ef2ad0b561c362c500bc84f36b6785
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: unset
 * Libcrux: bccb526ae5d7c8a8845745889b8996dfe9917915
 */

#ifndef libcrux_core_H
#define libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $3168size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_83_s {
  uint8_t value[3168U];
} libcrux_ml_kem_types_MlKemPrivateKey_83;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_64_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemPublicKey_64;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_83 sk;
  libcrux_ml_kem_types_MlKemPublicKey_64 pk;
} libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_64_s {
  uint8_t value[1568U];
} libcrux_ml_kem_types_MlKemCiphertext_64;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_d9_s {
  uint8_t value[2400U];
} libcrux_ml_kem_types_MlKemPrivateKey_d9;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_30_s {
  uint8_t value[1184U];
} libcrux_ml_kem_types_MlKemPublicKey_30;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_ml_kem_types_MlKemPublicKey_30 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

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
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1568size_t]],
uint8_t[32size_t]

*/
typedef struct tuple_fa_s {
  libcrux_ml_kem_types_MlKemCiphertext_64 fst;
  uint8_t snd[32U];
} tuple_fa;

#if defined(__cplusplus)
}
#endif

#define libcrux_core_H_DEFINED
#endif /* libcrux_core_H */
