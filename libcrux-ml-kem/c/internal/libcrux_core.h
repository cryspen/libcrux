/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: 3c77f1ac8116257d0c416fdac562edfa178b860b
 * Karamel: b2cba1e3f23fd7a54cf0b515f95089cfba8d39c3
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#ifndef internal_libcrux_core_H
#define internal_libcrux_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_core.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

static uint32_t core_num__u32__BITS = 32U;

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_arr_c4 x0);

static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1);

static inline Eurydice_arr_c4 core_num__u64__to_le_bytes(uint64_t x0);

uint8_t libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs);

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

Eurydice_arr_60
libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector);

Eurydice_arr_60
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s);

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_27_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int16_t libcrux_secrets_int_as_i16_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint8_t libcrux_secrets_int_as_u8_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self);

int16_t libcrux_secrets_int_I16(int16_t v);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int32_t libcrux_secrets_int_as_i32_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int16_t libcrux_secrets_int_as_i16_36(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int32_t libcrux_secrets_int_as_i32_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint16_t libcrux_secrets_int_as_u16_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
int16_t libcrux_secrets_int_as_i16_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_27_df(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int16_t libcrux_secrets_int_as_i16_b8(uint32_t self);

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_d3
with const generics
- SIZE= 1632
*/
Eurydice_arr_7f0 libcrux_ml_kem_types_default_d3_2a(void);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 800
*/
Eurydice_arr_30 libcrux_ml_kem_types_from_fd_4d(Eurydice_arr_30 value);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemKeyPair_3e libcrux_ml_kem_types_from_17_fa(
    Eurydice_arr_7f0 sk, Eurydice_arr_30 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 1632
*/
Eurydice_arr_7f0 libcrux_ml_kem_types_from_77_2a(Eurydice_arr_7f0 value);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e0
with const generics
- SIZE= 768
*/
Eurydice_arr_56 libcrux_ml_kem_types_from_e0_d0(Eurydice_arr_56 value);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 800
*/
Eurydice_arr_30 *libcrux_ml_kem_types_as_slice_e6_4d(Eurydice_arr_30 *self);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_a9
with const generics
- SIZE= 768
*/
Eurydice_arr_56 *libcrux_ml_kem_types_as_slice_a9_d0(Eurydice_arr_56 *self);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$128size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_a01_s {
  Eurydice_arr_d1 data[2U];
} Eurydice_arr_a01;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$192size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_a80_s {
  Eurydice_arr_f2 data[2U];
} Eurydice_arr_a80;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $33size_t
*/
typedef struct Eurydice_arr_3e_s {
  uint8_t data[33U];
} Eurydice_arr_3e;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_cf_s {
  Eurydice_arr_3e data[2U];
} Eurydice_arr_cf;

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 2
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_fd(Eurydice_arr_cf *prf_inputs,
                                              uint8_t domain_separator);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_a9_s {
  Eurydice_arr_27 data[2U];
} Eurydice_arr_a9;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $272size_t
*/
typedef struct Eurydice_arr_a00_s {
  int16_t data[272U];
} Eurydice_arr_a00;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_04_s {
  Eurydice_arr_a00 data[2U];
} Eurydice_arr_04;

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_fb_s {
  size_t data[2U];
} Eurydice_arr_fb;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_45_s {
  Eurydice_arr_b0 data[2U];
} Eurydice_arr_45;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $34size_t
*/
typedef struct Eurydice_arr_480_s {
  uint8_t data[34U];
} Eurydice_arr_480;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_340_s {
  Eurydice_arr_480 data[2U];
} Eurydice_arr_340;

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_d3_d0(Eurydice_arr_56 *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 800
*/
Eurydice_arr_30 libcrux_ml_kem_utils_into_padded_array_4d(Eurydice_slice slice);

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
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_0c(
    Eurydice_slice private_key);

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_d3
with const generics
- SIZE= 3168
*/
Eurydice_arr_17 libcrux_ml_kem_types_default_d3_39(void);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_ml_kem_types_from_fd_af(Eurydice_arr_00 value);

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_17
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_17_94(
    Eurydice_arr_17 sk, Eurydice_arr_00 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 3168
*/
Eurydice_arr_17 libcrux_ml_kem_types_from_77_39(Eurydice_arr_17 value);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e0
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 libcrux_ml_kem_types_from_e0_af(Eurydice_arr_00 value);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 *libcrux_ml_kem_types_as_slice_e6_af(Eurydice_arr_00 *self);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_a9
with const generics
- SIZE= 1568
*/
Eurydice_arr_00 *libcrux_ml_kem_types_as_slice_a9_af(Eurydice_arr_00 *self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $352size_t
*/
typedef struct Eurydice_arr_79_s {
  uint8_t data[352U];
} Eurydice_arr_79;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$128size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_cc0_s {
  Eurydice_arr_d1 data[4U];
} Eurydice_arr_cc0;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_65_s {
  Eurydice_arr_3e data[4U];
} Eurydice_arr_65;

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_ac(Eurydice_arr_65 *prf_inputs,
                                              uint8_t domain_separator);

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
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_8a_s {
  Eurydice_arr_a00 data[4U];
} Eurydice_arr_8a;

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_33_s {
  size_t data[4U];
} Eurydice_arr_33;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_ec_s {
  Eurydice_arr_b0 data[4U];
} Eurydice_arr_ec;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_78_s {
  Eurydice_arr_480 data[4U];
} Eurydice_arr_78;

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_d3_af(Eurydice_arr_00 *self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1600size_t
*/
typedef struct Eurydice_arr_e7_s {
  uint8_t data[1600U];
} Eurydice_arr_e7;

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
Eurydice_arr_e7 libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_slice slice);

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_1f(
    Eurydice_slice private_key);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 32
*/
Eurydice_arr_60 libcrux_ml_kem_utils_into_padded_array_9e(Eurydice_slice slice);

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_d3
with const generics
- SIZE= 2400
*/
Eurydice_arr_ea libcrux_ml_kem_types_default_d3_28(void);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 1184
*/
Eurydice_arr_74 libcrux_ml_kem_types_from_fd_d0(Eurydice_arr_74 value);

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
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_17_74(
    Eurydice_arr_ea sk, Eurydice_arr_74 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 2400
*/
Eurydice_arr_ea libcrux_ml_kem_types_from_77_28(Eurydice_arr_ea value);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $384size_t
*/
typedef struct Eurydice_arr_cc_s {
  uint8_t data[384U];
} Eurydice_arr_cc;

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_95_tags;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$32size_t]], core_array_TryFromSliceError

*/
typedef struct core_result_Result_95_s {
  core_result_Result_95_tags tag;
  union {
    Eurydice_arr_60 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_95;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$32size_t]], core_array_TryFromSliceError

*/
Eurydice_arr_60 core_result_unwrap_26_07(core_result_Result_95 self);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e0
with const generics
- SIZE= 1088
*/
Eurydice_arr_2c libcrux_ml_kem_types_from_e0_80(Eurydice_arr_2c value);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 1184
*/
Eurydice_arr_74 *libcrux_ml_kem_types_as_slice_e6_d0(Eurydice_arr_74 *self);

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_a9
with const generics
- SIZE= 1088
*/
Eurydice_arr_2c *libcrux_ml_kem_types_as_slice_a9_80(Eurydice_arr_2c *self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $320size_t
*/
typedef struct Eurydice_arr_b7_s {
  uint8_t data[320U];
} Eurydice_arr_b7;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_c1_s {
  int16_t data[256U];
} Eurydice_arr_c1;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$128size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_db_s {
  Eurydice_arr_d1 data[3U];
} Eurydice_arr_db;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_46_s {
  Eurydice_arr_3e data[3U];
} Eurydice_arr_46;

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(Eurydice_arr_46 *prf_inputs,
                                              uint8_t domain_separator);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
Eurydice_arr_3e libcrux_ml_kem_utils_into_padded_array_c8(Eurydice_slice slice);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
Eurydice_arr_480 libcrux_ml_kem_utils_into_padded_array_b6(
    Eurydice_slice slice);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_d6_s {
  Eurydice_arr_27 data[3U];
} Eurydice_arr_d6;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_d4_s {
  Eurydice_arr_a00 data[3U];
} Eurydice_arr_d4;

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_c8_s {
  size_t data[3U];
} Eurydice_arr_c8;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_35_s {
  Eurydice_arr_b0 data[3U];
} Eurydice_arr_35;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_84_s {
  Eurydice_arr_480 data[3U];
} Eurydice_arr_84;

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_d3_80(Eurydice_arr_2c *self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1120size_t
*/
typedef struct Eurydice_arr_48_s {
  uint8_t data[1120U];
} Eurydice_arr_48;

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
Eurydice_arr_48 libcrux_ml_kem_utils_into_padded_array_15(Eurydice_slice slice);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
libcrux_sha3_Sha3_512Digest libcrux_ml_kem_utils_into_padded_array_24(
    Eurydice_slice slice);

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
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_b4(
    Eurydice_slice private_key);

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option_1b_tags;

/**
A monomorphic instance of core.option.Option
with types Eurydice_slice uint8_t

*/
typedef struct core_option_Option_1b_s {
  core_option_Option_1b_tags tag;
  Eurydice_slice f0;
} core_option_Option_1b;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_e5_s {
  int16_t data[8U];
} Eurydice_arr_e5;

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$24size_t]]

*/
Eurydice_arr_6d libcrux_secrets_int_public_integers_declassify_d8_bd(
    Eurydice_arr_6d self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$20size_t]]

*/
Eurydice_arr_dc libcrux_secrets_int_public_integers_declassify_d8_89(
    Eurydice_arr_dc self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$8size_t]]

*/
Eurydice_arr_c4 libcrux_secrets_int_public_integers_declassify_d8_36(
    Eurydice_arr_c4 self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$2size_t]]

*/
Eurydice_arr_8b libcrux_secrets_int_public_integers_declassify_d8_ee0(
    Eurydice_arr_8b self);

/**
 Classify a mutable slice (identity)
 We define a separate function for this because hax has limited support for
 &mut-returning functions
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_mut_slice
with types Eurydice_slice uint8_t

*/
Eurydice_slice libcrux_secrets_int_public_integers_classify_mut_slice_ba(
    Eurydice_slice x);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_classify_27_3a(
    Eurydice_arr_e2 self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$22size_t]]

*/
Eurydice_arr_f3 libcrux_secrets_int_public_integers_declassify_d8_a9(
    Eurydice_arr_f3 self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$10size_t]]

*/
Eurydice_arr_77 libcrux_secrets_int_public_integers_declassify_d8_ed(
    Eurydice_arr_77 self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_slice int16_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_c5_03(
    Eurydice_slice *self);

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr int16_t[[$16size_t]], core_array_TryFromSliceError

*/
typedef struct core_result_Result_20_s {
  core_result_Result_95_tags tag;
  union {
    Eurydice_arr_e2 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_20;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr int16_t[[$16size_t]], core_array_TryFromSliceError

*/
Eurydice_arr_e2 core_result_unwrap_26_0e(core_result_Result_20 self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_e2 libcrux_secrets_int_public_integers_declassify_d8_3a(
    Eurydice_arr_e2 self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_slice uint8_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_c5_ba(
    Eurydice_slice *self);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_49_s {
  int16_t data[128U];
} Eurydice_arr_49;

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
A monomorphic instance of Eurydice.arr
with types core_core_arch_arm_shared_neon_uint64x2_t
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_4d_s {
  uint64x2_t data[5U];
} Eurydice_arr_4d;

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_e1_s {
  uint64_t data[2U];
} Eurydice_arr_e1;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_slice uint8_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_7d_s {
  Eurydice_slice data[2U];
} Eurydice_arr_7d;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $144size_t
*/
typedef struct Eurydice_arr_a8_s {
  uint8_t data[144U];
} Eurydice_arr_a8;

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
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_a5_s {
  uint64_t data[5U];
} Eurydice_arr_a5;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
typedef struct core_result_Result_a4_s {
  core_result_Result_95_tags tag;
  union {
    Eurydice_arr_c4 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_a4;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
Eurydice_arr_c4 core_result_unwrap_26_ab(core_result_Result_a4 self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1152size_t
*/
typedef struct Eurydice_arr_600_s {
  uint8_t data[1152U];
} Eurydice_arr_600;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  Eurydice_arr_600 fst;
  Eurydice_arr_74 snd;
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair512_s {
  Eurydice_arr_56 fst;
  Eurydice_arr_30 snd;
} libcrux_ml_kem_utils_extraction_helper_Keypair512;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1536size_t
*/
typedef struct Eurydice_arr_38_s {
  uint8_t data[1536U];
} Eurydice_arr_38;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair1024_s {
  Eurydice_arr_38 fst;
  Eurydice_arr_00 snd;
} libcrux_ml_kem_utils_extraction_helper_Keypair1024;

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_core_H_DEFINED
#endif /* internal_libcrux_core_H */
