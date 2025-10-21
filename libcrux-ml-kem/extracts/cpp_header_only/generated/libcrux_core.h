/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 1a15deb0a4af5c10c90c974891a6300b57adef8b
 * Karamel: d55e3f86aa758514f610dfe74f4f1807cdc7244f
 * F*: unset
 * Libcrux: 7627a1f4e6a01f57af3e70129ffa06d3d8e5db72
 */

#ifndef libcrux_core_H
#define libcrux_core_H

#include "eurydice_glue.h"

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_08_s {
  size_t start;
  size_t end;
} core_ops_range_Range_08;

/**
A monomorphic instance of core.ops.range.RangeTo
with types size_t

*/
typedef size_t core_ops_range_RangeTo_08;

/**
A monomorphic instance of core.ops.range.RangeFrom
with types size_t

*/
typedef size_t core_ops_range_RangeFrom_08;

#define Ok 0
#define Err 1

typedef uint8_t Result_10;

static inline Result_10
core_array__core__fmt__Debug_for_core__array__TryFromSliceError__fmt(
    TryFromSliceError *x0, core_fmt_Formatter *x1);

static inline bool core_cmp_impls__core__cmp__PartialEq_i32__for_i32__eq(
    int32_t *x0, int32_t *x1);

static inline bool core_cmp_impls__core__cmp__PartialEq_u32__for_u32__eq(
    uint32_t *x0, uint32_t *x1);

static inline bool core_cmp_impls__core__cmp__PartialEq_u8__for_u8__eq(
    uint8_t *x0, uint8_t *x1);

static inline bool core_cmp_impls__core__cmp__PartialEq_usize__for_usize__eq(
    size_t *x0, size_t *x1);

#define core_cmp_Ordering_Less -1
#define core_cmp_Ordering_Equal 0
#define core_cmp_Ordering_Greater 1

typedef int8_t core_cmp_Ordering;

#define None 0
#define Some 1

typedef uint8_t Option_77_tags;

/**
A monomorphic instance of core.option.Option
with types core_cmp_Ordering

*/
typedef struct Option_77_s {
  Option_77_tags tag;
  core_cmp_Ordering f0;
} Option_77;

static inline Option_77
core_cmp_impls__core__cmp__PartialOrd_i32__for_i32__partial_cmp(int32_t *x0,
                                                                int32_t *x1);

static inline Option_77
core_cmp_impls__core__cmp__PartialOrd_u32__for_u32__partial_cmp(uint32_t *x0,
                                                                uint32_t *x1);

static inline Option_77
core_cmp_impls__core__cmp__PartialOrd_usize__for_usize__partial_cmp(size_t *x0,
                                                                    size_t *x1);

static inline uint16_t core_num__u16__wrapping_add(uint16_t x0, uint16_t x1);

#define CORE_NUM__U32__MAX (~0U)

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_arr_c4 x0);

static inline uint64_t core_num__u64__rotate_left(uint64_t x0, uint32_t x1);

static inline Eurydice_arr_c4 core_num__u64__to_le_bytes(uint64_t x0);

static inline uint32_t core_num__u8__count_ones(uint8_t x0);

static inline uint8_t core_num__u8__wrapping_sub(uint8_t x0, uint8_t x1);

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
 Construct a public integer (identity)
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.secret
with types int16_t

*/
static KRML_MUSTINLINE int16_t
libcrux_secrets_int_public_integers_secret_39(int16_t x) {
  return x;
}

static KRML_MUSTINLINE int16_t libcrux_secrets_int_I16(int16_t v) {
  return libcrux_secrets_int_public_integers_secret_39(v);
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
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int64_t

*/
static KRML_MUSTINLINE int64_t
libcrux_secrets_int_public_integers_classify_27_b8(int64_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int8_t

*/
static KRML_MUSTINLINE int8_t
libcrux_secrets_int_public_integers_classify_27_ee(int8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE int16_t libcrux_secrets_int_as_i16_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE int32_t libcrux_secrets_int_as_i32_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE int64_t libcrux_secrets_int_as_i64_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_b8(
      (int64_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE int8_t libcrux_secrets_int_as_i8_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_ee(
      (int8_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint16_t libcrux_secrets_int_as_u16_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint32_t libcrux_secrets_int_as_u32_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint64_t libcrux_secrets_int_as_u64_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_49(
      (uint64_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint8_t libcrux_secrets_int_as_u8_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
A monomorphic instance of Eurydice.arr
with types core_fmt_rt_Argument
with const generics
- $0size_t
*/
typedef struct Eurydice_arr_7b_s {
  core_fmt_rt_Argument data[0U];
} Eurydice_arr_7b;

typedef struct Eurydice_str_s {
  Prims_string data;
  size_t len;
} Eurydice_str;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_str
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_7d_s {
  Eurydice_str data[1U];
} Eurydice_arr_7d;

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

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$24size_t]], core_array_TryFromSliceError

*/
typedef struct Result_16_s {
  Result_10 tag;
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
  Result_10 tag;
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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $10size_t
*/
typedef struct Eurydice_arr_77_s {
  uint8_t data[10U];
} Eurydice_arr_77;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$10size_t]], core_array_TryFromSliceError

*/
typedef struct Result_1c_s {
  Result_10 tag;
  union U {
    Eurydice_arr_77 case_Ok;
    TryFromSliceError case_Err;
  } val;
  KRML_UNION_CONSTRUCTOR(Result_1c_s)
} Result_1c;

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
with types Eurydice_slice uint8_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_d9_s {
  Eurydice_slice data[4U];
} Eurydice_arr_d9;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_600_s {
  uint8_t data[32U];
} Eurydice_arr_600;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$32size_t]], core_array_TryFromSliceError

*/
typedef struct Result_95_s {
  Result_10 tag;
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
A monomorphic instance of Eurydice.arr
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_46_s {
  Eurydice_arr_3e data[3U];
} Eurydice_arr_46;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $504size_t
*/
typedef struct Eurydice_arr_b0_s {
  uint8_t data[504U];
} Eurydice_arr_b0;

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
- $3size_t
*/
typedef struct Eurydice_arr_84_s {
  Eurydice_arr_480 data[3U];
} Eurydice_arr_84;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1120size_t
*/
typedef struct Eurydice_arr_48_s {
  uint8_t data[1120U];
} Eurydice_arr_48;

typedef struct Eurydice_slice_uint8_t_x2_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
} Eurydice_slice_uint8_t_x2;

typedef struct Eurydice_slice_uint8_t_x4_s {
  Eurydice_slice fst;
  Eurydice_slice snd;
  Eurydice_slice thd;
  Eurydice_slice f3;
} Eurydice_slice_uint8_t_x4;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1088size_t
*/
typedef struct Eurydice_arr_2c_s {
  uint8_t data[1088U];
} Eurydice_arr_2c;

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
with types Eurydice_arr uint8_t[[$10size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_77
libcrux_secrets_int_public_integers_declassify_d8_ed(Eurydice_arr_77 self) {
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
 Classify a mutable slice (identity)
 We define a separate function for this because hax has limited support for
 &mut-returning functions
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_mut_slice
with types Eurydice_slice uint8_t

*/
static KRML_MUSTINLINE Eurydice_slice
libcrux_secrets_int_public_integers_classify_mut_slice_ba(Eurydice_slice x) {
  return x;
}

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_e2_s {
  int16_t data[16U];
} Eurydice_arr_e2;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_e2
libcrux_secrets_int_public_integers_classify_27_3a(Eurydice_arr_e2 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr int16_t[[$16size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_e2
libcrux_secrets_int_public_integers_declassify_d8_3a(Eurydice_arr_e2 self) {
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
static KRML_MUSTINLINE Eurydice_slice
libcrux_secrets_int_classify_public_classify_ref_9b_90(Eurydice_slice self) {
  return self;
}

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $22size_t
*/
typedef struct Eurydice_arr_f3_s {
  uint8_t data[22U];
} Eurydice_arr_f3;

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$22size_t]]

*/
static KRML_MUSTINLINE Eurydice_arr_f3
libcrux_secrets_int_public_integers_declassify_d8_a9(Eurydice_arr_f3 self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a
(@Slice<T>)> for &'a (@Slice<T>)}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_9b
with types int16_t

*/
static KRML_MUSTINLINE Eurydice_slice
libcrux_secrets_int_classify_public_classify_ref_9b_39(Eurydice_slice self) {
  return self;
}

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr int16_t[[$16size_t]], core_array_TryFromSliceError

*/
typedef struct Result_20_s {
  Result_10 tag;
  union U {
    Eurydice_arr_e2 case_Ok;
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
static inline Eurydice_arr_e2 unwrap_26_0e(Result_20 self) {
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

typedef struct libcrux_sha3_Sha3_512Digest_s {
  uint8_t data[64U];
} libcrux_sha3_Sha3_512Digest;

typedef struct libcrux_sha3_Sha3_384Digest_s {
  uint8_t data[48U];
} libcrux_sha3_Sha3_384Digest;

typedef struct libcrux_sha3_Sha3_224Digest_s {
  uint8_t data[28U];
} libcrux_sha3_Sha3_224Digest;

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
A monomorphic instance of Eurydice.arr
with types Eurydice_slice uint8_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_34_s {
  Eurydice_slice data[1U];
} Eurydice_arr_34;

/**
A monomorphic instance of core.result.Result
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
typedef struct Result_a4_s {
  Result_10 tag;
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
with types uint8_t
with const generics
- $1184size_t
*/
typedef struct Eurydice_arr_74_s {
  uint8_t data[1184U];
} Eurydice_arr_74;

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
- $800size_t
*/
typedef struct Eurydice_arr_30_s {
  uint8_t data[800U];
} Eurydice_arr_30;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1568size_t
*/
typedef struct Eurydice_arr_00_s {
  uint8_t data[1568U];
} Eurydice_arr_00;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1536size_t
*/
typedef struct Eurydice_arr_38_s {
  uint8_t data[1536U];
} Eurydice_arr_38;

/**
A monomorphic instance of core.option.Option
with types uint32_t

*/
typedef struct Option_7e_s {
  Option_77_tags tag;
  uint32_t f0;
} Option_7e;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct Option_08_s {
  Option_77_tags tag;
  size_t f0;
} Option_08;

/**
A monomorphic instance of core.option.Option
with types int32_t

*/
typedef struct Option_9e_s {
  Option_77_tags tag;
  int32_t f0;
} Option_9e;

#define libcrux_core_H_DEFINED
#endif /* libcrux_core_H */
