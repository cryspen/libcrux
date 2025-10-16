/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9b87e8727803cd306b94c18b0ceb0b5b1c18c0e9
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */


#ifndef libcrux_core_H
#define libcrux_core_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_60_s { uint8_t data[32U]; } Eurydice_arr_60;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1632size_t
*/
typedef struct Eurydice_arr_7f0_s { uint8_t data[1632U]; } Eurydice_arr_7f0;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $800size_t
*/
typedef struct Eurydice_arr_30_s { uint8_t data[800U]; } Eurydice_arr_30;

/**
A monomorphic instance of libcrux_ml_kem.types.MlKemKeyPair
with const generics
- $1632size_t
- $800size_t
*/
typedef struct libcrux_ml_kem_types_MlKemKeyPair_3e_s
{
  Eurydice_arr_7f0 sk;
  Eurydice_arr_30 pk;
}
libcrux_ml_kem_types_MlKemKeyPair_3e;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $768size_t
*/
typedef struct Eurydice_arr_56_s { uint8_t data[768U]; } Eurydice_arr_56;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$768size_t]], Eurydice_arr uint8_t[[$32size_t]]

*/
typedef struct tuple_17_s
{
  Eurydice_arr_56 fst;
  Eurydice_arr_60 snd;
}
tuple_17;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_d1_s { uint8_t data[128U]; } Eurydice_arr_d1;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $192size_t
*/
typedef struct Eurydice_arr_f2_s { uint8_t data[192U]; } Eurydice_arr_f2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $168size_t
*/
typedef struct Eurydice_arr_27_s { uint8_t data[168U]; } Eurydice_arr_27;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $504size_t
*/
typedef struct Eurydice_arr_b0_s { uint8_t data[504U]; } Eurydice_arr_b0;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3168size_t
*/
typedef struct Eurydice_arr_17_s { uint8_t data[3168U]; } Eurydice_arr_17;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1568size_t
*/
typedef struct Eurydice_arr_00_s { uint8_t data[1568U]; } Eurydice_arr_00;

typedef struct libcrux_ml_kem_mlkem1024_MlKem1024KeyPair_s
{
  Eurydice_arr_17 sk;
  Eurydice_arr_00 pk;
}
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1568size_t]], Eurydice_arr uint8_t[[$32size_t]]

*/
typedef struct tuple_2b_s
{
  Eurydice_arr_00 fst;
  Eurydice_arr_60 snd;
}
tuple_2b;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2400size_t
*/
typedef struct Eurydice_arr_ea_s { uint8_t data[2400U]; } Eurydice_arr_ea;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1184size_t
*/
typedef struct Eurydice_arr_74_s { uint8_t data[1184U]; } Eurydice_arr_74;

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s
{
  Eurydice_arr_ea sk;
  Eurydice_arr_74 pk;
}
libcrux_ml_kem_mlkem768_MlKem768KeyPair;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1088size_t
*/
typedef struct Eurydice_arr_2c_s { uint8_t data[1088U]; } Eurydice_arr_2c;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]], Eurydice_arr uint8_t[[$32size_t]]

*/
typedef struct tuple_56_s
{
  Eurydice_arr_2c fst;
  Eurydice_arr_60 snd;
}
tuple_56;

typedef struct libcrux_sha3_Sha3_512Digest_s { uint8_t data[64U]; }
libcrux_sha3_Sha3_512Digest;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_6d_s { uint8_t data[24U]; } Eurydice_arr_6d;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $20size_t
*/
typedef struct Eurydice_arr_dc_s { uint8_t data[20U]; } Eurydice_arr_dc;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_e2_s { int16_t data[16U]; } Eurydice_arr_e2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $22size_t
*/
typedef struct Eurydice_arr_f3_s { uint8_t data[22U]; } Eurydice_arr_f3;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $10size_t
*/
typedef struct Eurydice_arr_77_s { uint8_t data[10U]; } Eurydice_arr_77;

/**
A monomorphic instance of Eurydice.arr
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_fe_s { uint64x2_t data[25U]; } Eurydice_arr_fe;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_3d_s { uint8_t data[136U]; } Eurydice_arr_3d;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$136size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_c40_s { Eurydice_arr_3d data[1U]; } Eurydice_arr_c40;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_75_s { Eurydice_arr_27 data[1U]; } Eurydice_arr_75;

typedef struct libcrux_sha3_Sha3_384Digest_s { uint8_t data[48U]; }
libcrux_sha3_Sha3_384Digest;

typedef struct libcrux_sha3_Sha3_224Digest_s { uint8_t data[28U]; }
libcrux_sha3_Sha3_224Digest;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_slice uint8_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_34_s { Eurydice_slice data[1U]; } Eurydice_arr_34;

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_26_s { uint64_t data[25U]; } Eurydice_arr_26;

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_a7_s { uint64_t data[24U]; } Eurydice_arr_a7;

#if defined(__cplusplus)
}
#endif

#define libcrux_core_H_DEFINED
#endif /* libcrux_core_H */
