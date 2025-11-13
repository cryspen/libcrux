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
 * Libcrux: 55a15c0abfa4a1326744575999e590ebcd72ec30
 */

#ifndef libcrux_mlkem_core_H
#define libcrux_mlkem_core_H

#include "eurydice_glue.h"

static inline uint16_t core_num__u16__wrapping_add(uint16_t x0, uint16_t x1);

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_arr_c4 x0);

static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1);

static inline Eurydice_arr_c4 core_num__u64__to_le_bytes(uint64_t x0);

static inline uint32_t core_num__u8__count_ones(uint8_t x0);

static inline uint8_t core_num__u8__wrapping_sub(uint8_t x0, uint8_t x1);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

#define LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE ((size_t)32U)

#define LIBCRUX_ML_KEM_CONSTANTS_G_DIGEST_SIZE ((size_t)64U)

#define LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
static inline size_t libcrux_ml_kem_constants_ranked_bytes_per_ring_element(
    size_t rank) {
  return rank * LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t
libcrux_secrets_int_public_integers_classify_27_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
static KRML_MUSTINLINE int16_t
libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
static KRML_MUSTINLINE int16_t
libcrux_secrets_int_public_integers_classify_27_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t
libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
static KRML_MUSTINLINE int32_t
libcrux_secrets_int_public_integers_classify_27_a8(int32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int32_t

*/
static KRML_MUSTINLINE int32_t
libcrux_secrets_int_public_integers_declassify_d8_a8(int32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_declassify_d8_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t
libcrux_secrets_int_public_integers_classify_27_de(uint16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t
libcrux_secrets_int_public_integers_declassify_d8_de(uint16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_classify_27_49(uint64_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t
libcrux_secrets_int_public_integers_classify_27_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t
libcrux_secrets_int_public_integers_declassify_d8_49(uint64_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1152size_t
*/
typedef struct Eurydice_arr_60_s {
  uint8_t data[1152U];
} Eurydice_arr_60;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1184size_t
*/
typedef struct Eurydice_arr_74_s {
  uint8_t data[1184U];
} Eurydice_arr_74;

typedef struct libcrux_ml_kem_utils_extraction_helper_Keypair768_s {
  Eurydice_arr_60 fst;
  Eurydice_arr_74 snd;
} libcrux_ml_kem_utils_extraction_helper_Keypair768;

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
with types Eurydice_arr uint8_t[[$16size_t]]
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_ef_s {
  Eurydice_arr_88 data[256U];
} Eurydice_arr_ef;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_6d_s {
  uint8_t data[24U];
} Eurydice_arr_6d;

#define Ok 0
#define Err 1

typedef uint8_t Result_16_tags;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$24size_t]], core_array_TryFromSliceError

*/
typedef struct Result_16_s {
  Result_16_tags tag;
  union U {
    Eurydice_arr_6d case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_16_s)
} Result_16;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$24size_t]], core_array_TryFromSliceError

*/
static inline Eurydice_arr_6d unwrap_26_a9(Result_16 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $20size_t
*/
typedef struct Eurydice_arr_dc_s {
  uint8_t data[20U];
} Eurydice_arr_dc;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$20size_t]], core_array_TryFromSliceError

*/
typedef struct Result_6e_s {
  Result_16_tags tag;
  union U {
    Eurydice_arr_dc case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_6e_s)
} Result_6e;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$20size_t]], core_array_TryFromSliceError

*/
static inline Eurydice_arr_dc unwrap_26_51(Result_6e self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 16
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3616(
    Eurydice_arr_88 *a, core_ops_range_Range_08 r) {
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
with types int16_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_e20_s {
  int16_t data[16U];
} Eurydice_arr_e20;

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
with types Eurydice_dst_ref uint8_t size_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_66_s {
  Eurydice_dst_ref_87 data[4U];
} Eurydice_arr_66;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_600_s {
  uint8_t data[32U];
} Eurydice_arr_600;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_366(
    Eurydice_arr_600 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_600
libcrux_ml_kem_utils_into_padded_array_9e(Eurydice_dst_ref_87 slice) {
  Eurydice_arr_600 out = {{0U}};
  Eurydice_arr_600 *uu____0 = &out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_366(
          uu____0, (core_ops_range_Range_08{
                       (size_t)0U, Eurydice_slice_len(slice, uint8_t)})),
      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2400size_t
*/
typedef struct Eurydice_arr_ea_s {
  uint8_t data[2400U];
} Eurydice_arr_ea;

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.default_d3
with const generics
- SIZE= 2400
*/
static inline Eurydice_arr_ea libcrux_ml_kem_types_default_d3_28(void) {
  return (Eurydice_arr_ea{{0U}});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_to_6e(
    Eurydice_arr_74 *a, size_t r) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_fd
with const generics
- SIZE= 1184
*/
static inline Eurydice_arr_74 libcrux_ml_kem_types_from_fd_d0(
    Eurydice_arr_74 value) {
  return value;
}

typedef struct libcrux_ml_kem_mlkem768_MlKem768KeyPair_s {
  Eurydice_arr_ea sk;
  Eurydice_arr_74 pk;
} libcrux_ml_kem_mlkem768_MlKem768KeyPair;

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
static inline libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types_from_17_74(Eurydice_arr_ea sk, Eurydice_arr_74 pk) {
  return (libcrux_ml_kem_mlkem768_MlKem768KeyPair{sk, pk});
}

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_77
with const generics
- SIZE= 2400
*/
static inline Eurydice_arr_ea libcrux_ml_kem_types_from_77_28(
    Eurydice_arr_ea value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3615(
    Eurydice_arr_ea *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1152
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_06(
    Eurydice_arr_60 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1152U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_from_8c2(
    Eurydice_arr_74 *a, size_t r) {
  return (Eurydice_dst_ref_87{a->data + r, (size_t)1184U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1184
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3614(
    Eurydice_arr_74 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 24
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_0b(
    Eurydice_arr_6d *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)24U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $384size_t
*/
typedef struct Eurydice_arr_cc_s {
  uint8_t data[384U];
} Eurydice_arr_cc;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 384
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3613(
    Eurydice_arr_cc *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 384
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_fe(
    Eurydice_arr_cc *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)384U;
  return lit;
}

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$32size_t]], core_array_TryFromSliceError

*/
typedef struct Result_95_s {
  Result_16_tags tag;
  union U {
    Eurydice_arr_600 case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_95_s)
} Result_95;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$32size_t]], core_array_TryFromSliceError

*/
static inline Eurydice_arr_600 unwrap_26_07(Result_95 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1088size_t
*/
typedef struct Eurydice_arr_2c_s {
  uint8_t data[1088U];
} Eurydice_arr_2c;

/**
A monomorphic instance of K.
with types libcrux_ml_kem_types_MlKemCiphertext[[$1088size_t]], Eurydice_arr
uint8_t[[$32size_t]]

*/
typedef struct tuple_56_s {
  Eurydice_arr_2c fst;
  Eurydice_arr_600 snd;
} tuple_56;

/**
This function found in impl {core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_e0
with const generics
- SIZE= 1088
*/
static inline Eurydice_arr_2c libcrux_ml_kem_types_from_e0_80(
    Eurydice_arr_2c value) {
  return value;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_e6
with const generics
- SIZE= 1184
*/
static inline Eurydice_arr_74 *libcrux_ml_kem_types_as_slice_e6_d0(
    Eurydice_arr_74 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1184
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_45(
    Eurydice_arr_74 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1184U;
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_a9
with const generics
- SIZE= 1088
*/
static inline Eurydice_arr_2c *libcrux_ml_kem_types_as_slice_a9_80(
    Eurydice_arr_2c *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 20
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_c2(
    Eurydice_arr_dc *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)20U;
  return lit;
}

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
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 320
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3612(
    Eurydice_arr_b7 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 320
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_d3(
    Eurydice_arr_b7 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)320U;
  return lit;
}

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
A monomorphic instance of Eurydice.array_to_slice
with types int16_t
with const generics
- N= 256
*/
static inline Eurydice_dst_ref_9a Eurydice_array_to_slice_1a(
    Eurydice_arr_c1 *a) {
  Eurydice_dst_ref_9a lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
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
with types uint8_t
with const generics
- $33size_t
*/
typedef struct Eurydice_arr_3e_s {
  uint8_t data[33U];
} Eurydice_arr_3e;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 33
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_61(
    Eurydice_arr_3e *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)33U;
  return lit;
}

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
static KRML_MUSTINLINE uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(
    Eurydice_arr_46 *prf_inputs, uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs->data[i0].data[32U] = domain_separator;
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 33
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3611(
    Eurydice_arr_3e *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
static KRML_MUSTINLINE Eurydice_arr_3e
libcrux_ml_kem_utils_into_padded_array_c8(Eurydice_dst_ref_87 slice) {
  Eurydice_arr_3e out = {{0U}};
  Eurydice_arr_3e *uu____0 = &out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_3611(
          uu____0, (core_ops_range_Range_08{
                       (size_t)0U, Eurydice_slice_len(slice, uint8_t)})),
      slice, uint8_t);
  return out;
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
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_3610(
    Eurydice_arr_48 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
static KRML_MUSTINLINE Eurydice_arr_48
libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_dst_ref_87 slice) {
  Eurydice_arr_48 out = {{0U}};
  Eurydice_arr_48 *uu____0 = &out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_3610(
          uu____0, (core_ops_range_Range_08{
                       (size_t)0U, Eurydice_slice_len(slice, uint8_t)})),
      slice, uint8_t);
  return out;
}

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
A monomorphic instance of Eurydice.array_to_subslice
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 272
*/
static inline Eurydice_dst_ref_9a Eurydice_array_to_subslice_850(
    Eurydice_arr_a00 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_9a{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $504size_t
*/
typedef struct Eurydice_arr_b0_s {
  uint8_t data[504U];
} Eurydice_arr_b0;

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 504
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_369(
    Eurydice_arr_b0 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

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
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 504
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_85(
    Eurydice_arr_b0 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)504U;
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_84_s {
  Eurydice_arr_48 data[3U];
} Eurydice_arr_84;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1120size_t
*/
typedef struct Eurydice_arr_480_s {
  uint8_t data[1120U];
} Eurydice_arr_480;

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1120
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_74(
    Eurydice_arr_480 *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1120U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 1088
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_42(
    Eurydice_arr_2c *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1088U;
  return lit;
}

/**
This function found in impl {core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_d3
with const generics
- SIZE= 1088
*/
static inline Eurydice_dst_ref_87 libcrux_ml_kem_types_as_ref_d3_80(
    Eurydice_arr_2c *self) {
  return Eurydice_array_to_slice_42(self);
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1120
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_from_8c1(
    Eurydice_arr_480 *a, size_t r) {
  return (Eurydice_dst_ref_87{a->data + r, (size_t)1120U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1120
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_368(
    Eurydice_arr_480 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
static KRML_MUSTINLINE Eurydice_arr_480
libcrux_ml_kem_utils_into_padded_array_15(Eurydice_dst_ref_87 slice) {
  Eurydice_arr_480 out = {{0U}};
  Eurydice_arr_480 *uu____0 = &out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_368(
          uu____0, (core_ops_range_Range_08{
                       (size_t)0U, Eurydice_slice_len(slice, uint8_t)})),
      slice, uint8_t);
  return out;
}

typedef struct libcrux_sha3_Sha3_512Digest_s {
  uint8_t data[64U];
} libcrux_sha3_Sha3_512Digest;

/**
A monomorphic instance of Eurydice.array_to_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_from_8c0(
    libcrux_sha3_Sha3_512Digest *a, size_t r) {
  return (Eurydice_dst_ref_87{a->data + r, (size_t)64U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_367(
    libcrux_sha3_Sha3_512Digest *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
libcrux_ml_kem_utils_into_padded_array_24(Eurydice_dst_ref_87 slice) {
  libcrux_sha3_Sha3_512Digest out = {{0U}};
  libcrux_sha3_Sha3_512Digest *uu____0 = &out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_367(
          uu____0, (core_ops_range_Range_08{
                       (size_t)0U, Eurydice_slice_len(slice, uint8_t)})),
      slice, uint8_t);
  return out;
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
A monomorphic instance of Eurydice.array_to_subslice_from
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_from_8c(
    Eurydice_arr_2c *a, size_t r) {
  return (Eurydice_dst_ref_87{a->data + r, (size_t)1088U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1088
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_365(
    Eurydice_arr_2c *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice
with types uint8_t
with const generics
- N= 2400
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_slice_ec(
    Eurydice_arr_ea *a) {
  Eurydice_dst_ref_87 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2400U;
  return lit;
}

typedef struct Eurydice_dst_ref_uint8_t_size_t_x4_s {
  Eurydice_dst_ref_87 fst;
  Eurydice_dst_ref_87 snd;
  Eurydice_dst_ref_87 thd;
  Eurydice_dst_ref_87 f3;
} Eurydice_dst_ref_uint8_t_size_t_x4;

typedef struct Eurydice_dst_ref_uint8_t_size_t_x2_s {
  Eurydice_dst_ref_87 fst;
  Eurydice_dst_ref_87 snd;
} Eurydice_dst_ref_uint8_t_size_t_x2;

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
static inline Eurydice_dst_ref_uint8_t_size_t_x4
libcrux_ml_kem_types_unpack_private_key_b4(Eurydice_dst_ref_87 private_key) {
  Eurydice_dst_ref_uint8_t_size_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_dst_ref_uint8_t_size_t_x2);
  Eurydice_dst_ref_87 ind_cpa_secret_key = uu____0.fst;
  Eurydice_dst_ref_87 secret_key0 = uu____0.snd;
  Eurydice_dst_ref_uint8_t_size_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_dst_ref_uint8_t_size_t_x2);
  Eurydice_dst_ref_87 ind_cpa_public_key = uu____1.fst;
  Eurydice_dst_ref_87 secret_key = uu____1.snd;
  Eurydice_dst_ref_uint8_t_size_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_dst_ref_uint8_t_size_t_x2);
  Eurydice_dst_ref_87 ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_dst_ref_87 implicit_rejection_value = uu____2.snd;
  return (Eurydice_dst_ref_uint8_t_size_t_x4{
      ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash,
      implicit_rejection_value});
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$24size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_6d
libcrux_secrets_int_public_integers_declassify_d8_bd(Eurydice_arr_6d self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$20size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_dc
libcrux_secrets_int_public_integers_declassify_d8_89(Eurydice_arr_dc self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$8size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_c4
libcrux_secrets_int_public_integers_declassify_d8_36(Eurydice_arr_c4 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$2size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_8b
libcrux_secrets_int_public_integers_declassify_d8_ee(Eurydice_arr_8b self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_e20
libcrux_secrets_int_public_integers_classify_27_3a(Eurydice_arr_e20 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types uint8_t

*/
static KRML_MUSTINLINE Eurydice_dst_ref_87
libcrux_secrets_int_classify_public_classify_ref_9b_90(
    Eurydice_dst_ref_87 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 16
*/
static inline Eurydice_dst_ref_9a Eurydice_array_to_subslice_85(
    Eurydice_arr_e20 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_9a{a->data + r.start, r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types int16_t

*/
static KRML_MUSTINLINE Eurydice_dst_ref_9a
libcrux_secrets_int_classify_public_classify_ref_9b_39(
    Eurydice_dst_ref_9a self) {
  return self;
}

/**
A monomorphic instance of Eurydice.slice_subslice
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
static inline Eurydice_dst_ref_9a Eurydice_slice_subslice_76(
    Eurydice_dst_ref_9a s, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_9a{s.ptr + r.start, r.end - r.start});
}

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr int16_t[[$16size_t]], core_array_TryFromSliceError

*/
typedef struct Result_20_s {
  Result_16_tags tag;
  union U {
    Eurydice_arr_e20 case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_20_s)
} Result_20;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr int16_t[[$16size_t]], core_array_TryFromSliceError

*/
static inline Eurydice_arr_e20 unwrap_26_0e(Result_20 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

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
A monomorphic instance of Eurydice.dst_ref
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_fc_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_fc;

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
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_75_s {
  Eurydice_arr_27 data[1U];
} Eurydice_arr_75;

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
    Eurydice_arr_600 *a) {
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
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_364(
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
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_363(
    Eurydice_arr_a8 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

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
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_362(
    Eurydice_arr_27 *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
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
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_361(
    Eurydice_arr_3d *a, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{a->data + r.start, r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 8
*/
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_360(
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
static inline Eurydice_dst_ref_87 Eurydice_array_to_subslice_36(
    Eurydice_arr_a0 *a, core_ops_range_Range_08 r) {
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
A monomorphic instance of Eurydice.slice_subslice
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
static inline Eurydice_dst_ref_87 Eurydice_slice_subslice_7e(
    Eurydice_dst_ref_87 s, core_ops_range_Range_08 r) {
  return (Eurydice_dst_ref_87{s.ptr + r.start, r.end - r.start});
}

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
typedef struct Result_a4_s {
  Result_16_tags tag;
  union U {
    Eurydice_arr_c4 case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_a4_s)
} Result_a4;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
static inline Eurydice_arr_c4 unwrap_26_ab(Result_a4 self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_26_s {
  uint64_t data[25U];
} Eurydice_arr_26;

/**
A monomorphic instance of Eurydice.arr
with types uint64_t
with const generics
- $24size_t
*/
typedef struct Eurydice_arr_a7_s {
  uint64_t data[24U];
} Eurydice_arr_a7;

#define libcrux_mlkem_core_H_DEFINED
#endif /* libcrux_mlkem_core_H */
