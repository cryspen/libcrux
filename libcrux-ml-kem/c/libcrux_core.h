/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 5807deab3f588567f00046b8ee83e4eba7cff5f6
 * Eurydice: 924e44f2e6e8caac37cddca618ba9488f0990ccc
 * Karamel: c56e0932f05c89c8c68089d909ad9c195f44a02c
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: 85ef3af5e4511668b215821a564d6537be61d44c
 */


#ifndef __libcrux_core_H
#define __libcrux_core_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $3168size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_83_s { uint8_t value[3168U]; }
libcrux_ml_kem_types_MlKemPrivateKey_83;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_64_s { uint8_t value[1568U]; }
libcrux_ml_kem_types_MlKemPublicKey_64;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s
{
  libcrux_ml_kem_types_MlKemPrivateKey_83 sk;
  libcrux_ml_kem_types_MlKemPublicKey_64 pk;
}
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $1568size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_64_s { uint8_t value[1568U]; }
libcrux_ml_kem_types_MlKemCiphertext_64;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $2400size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_d9_s { uint8_t value[2400U]; }
libcrux_ml_kem_types_MlKemPrivateKey_d9;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $1184size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_30_s { uint8_t value[1184U]; }
libcrux_ml_kem_types_MlKemPublicKey_30;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s
{
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk;
  libcrux_ml_kem_types_MlKemPublicKey_30 pk;
}
libcrux_ml_kem_mlkem768_MlKem768KeyPair;

typedef struct libcrux_ml_kem_mlkem768_MlKem768Ciphertext_s { uint8_t value[1088U]; }
libcrux_ml_kem_mlkem768_MlKem768Ciphertext;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPrivateKey
with const generics
- $1632size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPrivateKey_fa_s { uint8_t value[1632U]; }
libcrux_ml_kem_types_MlKemPrivateKey_fa;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemPublicKey
with const generics
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemPublicKey_52_s { uint8_t value[800U]; }
libcrux_ml_kem_types_MlKemPublicKey_52;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemKeyPair
with const generics
- $1632size_t
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemKeyPair_3e_s
{
  libcrux_ml_kem_types_MlKemPrivateKey_fa sk;
  libcrux_ml_kem_types_MlKemPublicKey_52 pk;
}
libcrux_ml_kem_types_MlKemKeyPair_3e;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemCiphertext
with const generics
- $768size_t
*/
typedef struct libcrux_ml_kem_types_MlKemCiphertext_1a_s { uint8_t value[768U]; }
libcrux_ml_kem_types_MlKemCiphertext_1a;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]], uint8_t[32size_t]

*/
typedef struct tuple_c2_s
{
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext fst;
  uint8_t snd[32U];
}
tuple_c2;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$768size_t]], uint8_t[32size_t]

*/
typedef struct tuple_41_s
{
  libcrux_ml_kem_types_MlKemCiphertext_1a fst;
  uint8_t snd[32U];
}
tuple_41;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1568size_t]], uint8_t[32size_t]

*/
typedef struct tuple_fa_s
{
  libcrux_ml_kem_types_MlKemCiphertext_64 fst;
  uint8_t snd[32U];
}
tuple_fa;

#if defined(__cplusplus)
}
#endif

#define __libcrux_core_H_DEFINED
#endif
