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
 * Libcrux: bf73a8a7a0f119e66b105a3462265b4a2a3af63b
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

static inline uint64_t core_num__u64__from_le_bytes(uint8_t x0[8U]);

static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1);

static inline void core_num__u64__to_le_bytes(uint64_t x0, uint8_t x1[8U]);

void libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s, Eurydice_slice out);

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

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
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self);

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
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self);

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
    libcrux_ml_kem_types_MlKemPrivateKey_83 sk,
    libcrux_ml_kem_types_MlKemPublicKey_64 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_83 libcrux_ml_kem_types_from_77_39(
    uint8_t value[3168U]);

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_73
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemCiphertext_64 libcrux_ml_kem_types_default_73_af(
    void);

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
    libcrux_ml_kem_types_MlKemPrivateKey_d9 sk,
    libcrux_ml_kem_types_MlKemPublicKey_30 pk);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_d9 libcrux_ml_kem_types_from_77_28(
    uint8_t value[2400U]);

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_73
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_default_73_80(
    void);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_e6_d0(
    libcrux_ml_kem_types_MlKemPublicKey_30 *self);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_30 libcrux_ml_kem_types_from_fd_d0(
    uint8_t value[1184U]);

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
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_b4(
    Eurydice_slice private_key);

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator);

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_d3_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
void libcrux_ml_kem_utils_into_padded_array_15(Eurydice_slice slice,
                                               uint8_t ret[1120U]);

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_e6_af(
    libcrux_ml_kem_types_MlKemPublicKey_64 *self);

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_64 libcrux_ml_kem_types_from_fd_af(
    uint8_t value[1568U]);

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

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_fb_tags;

/**
A monomorphic instance of core.result.Result
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_fb_s {
  core_result_Result_fb_tags tag;
  union {
    uint8_t case_Ok[32U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_fb;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_b3(core_result_Result_fb self, uint8_t ret[32U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
void libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_slice slice,
                                               uint8_t ret[34U]);

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_ac(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
void libcrux_ml_kem_utils_into_padded_array_c8(Eurydice_slice slice,
                                               uint8_t ret[33U]);

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_d3_af(
    libcrux_ml_kem_types_MlKemCiphertext_64 *self);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_slice slice,
                                               uint8_t ret[1600U]);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
void libcrux_ml_kem_utils_into_padded_array_24(Eurydice_slice slice,
                                               uint8_t ret[64U]);

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
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types uint8_t

*/
Eurydice_slice libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_slice self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_declassify_d8_46(int16_t self[16U],
                                                          int16_t ret[16U]);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types int16_t

*/
Eurydice_slice libcrux_secrets_int_classify_public_classify_ref_9b_39(
    Eurydice_slice self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_classify_27_46(int16_t self[16U],
                                                        int16_t ret[16U]);

/**
A monomorphic instance of core.result.Result
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
typedef struct core_result_Result_15_s {
  core_result_Result_fb_tags tag;
  union {
    uint8_t case_Ok[8U];
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_15;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_68(core_result_Result_15 self, uint8_t ret[8U]);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_core_H_DEFINED
#endif /* internal_libcrux_core_H */
