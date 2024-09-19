/*
 * SPDX-FileCopyrightText: 2024 Eurydice Contributors
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 */

#pragma once

#if defined(__cplusplus)
extern "C" {
#endif

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "karamel/target.h"

// SLICES, ARRAYS, ETC.

// The MSVC C++ compiler does not support compound literals.
// This CLITERAL is used to turn `(type){...}` into `type{...}` when using a C++
// compiler.
#if defined(__cplusplus)
#define CLITERAL(type) type
#else
#define CLITERAL(type) (type)
#endif

// We represent a slice as a pair of an (untyped) pointer, along with the length
// of the slice, i.e. the number of elements in the slice (this is NOT the
// number of bytes). This design choice has two important consequences.
// - if you need to use `ptr`, you MUST cast it to a proper type *before*
// performing pointer
//   arithmetic on it (remember that C desugars pointer arithmetic based on the
//   type of the address)
// - if you need to use `len` for a C style function (e.g. memcpy, memcmp), you
// need to multiply it
//   by sizeof t, where t is the type of the elements.
//
// Empty slices have `len == 0` and `ptr` always needs to be valid pointer that
// is not NULL (otherwise the construction in EURYDICE_SLICE computes `NULL +
// start`).
typedef struct {
  void *ptr;
  size_t len;
} Eurydice_slice;

// Helper macro to create a slice out of a pointer x, a start index in x
// (included), and an end index in x (excluded). The argument x must be suitably
// cast to something that can decay (see remark above about how pointer
// arithmetic works in C), meaning either pointer or array type.
#define EURYDICE_SLICE(x, start, end) \
  (CLITERAL(Eurydice_slice){.ptr = (void *)(x + start), .len = end - start})
#define EURYDICE_SLICE_LEN(s, _) s.len
// This macro is a pain because in case the dereferenced element type is an
// array, you cannot simply write `t x` as it would yield `int[4] x` instead,
// which is NOT correct C syntax, so we add a dedicated phase in Eurydice that
// adds an extra argument to this macro at the last minute so that we have the
// correct type of *pointers* to elements.
#define Eurydice_slice_index(s, i, t, t_ptr_t) (((t_ptr_t)s.ptr)[i])
#define Eurydice_slice_subslice(s, r, t, _) \
  EURYDICE_SLICE((t *)s.ptr, r.start, r.end)
// Variant for when the start and end indices are statically known (i.e., the
// range argument `r` is a literal).
#define Eurydice_slice_subslice2(s, start, end, t) \
  EURYDICE_SLICE((t *)s.ptr, start, end)
#define Eurydice_slice_subslice_to(s, subslice_end_pos, t, _) \
  EURYDICE_SLICE((t *)s.ptr, 0, subslice_end_pos)
#define Eurydice_slice_subslice_from(s, subslice_start_pos, t, _) \
  EURYDICE_SLICE((t *)s.ptr, subslice_start_pos, s.len)
#define Eurydice_array_to_slice(end, x, t) \
  EURYDICE_SLICE(x, 0,                     \
                 end) /* x is already at an array type, no need for cast */
#define Eurydice_array_to_subslice(_arraylen, x, r, t, _) \
  EURYDICE_SLICE((t *)x, r.start, r.end)
// Same as above, variant for when start and end are statically known
#define Eurydice_array_to_subslice2(x, start, end, t) \
  EURYDICE_SLICE((t *)x, start, end)
#define Eurydice_array_to_subslice_to(_size, x, r, t, _range_t) \
  EURYDICE_SLICE((t *)x, 0, r)
#define Eurydice_array_to_subslice_from(size, x, r, t, _range_t) \
  EURYDICE_SLICE((t *)x, r, size)
#define Eurydice_slice_len(s, t) EURYDICE_SLICE_LEN(s, t)
#define Eurydice_slice_copy(dst, src, t) \
  memcpy(dst.ptr, src.ptr, dst.len * sizeof(t))
#define core_array___Array_T__N__23__as_slice(len_, ptr_, t, _ret_t) \
  ((Eurydice_slice){.ptr = ptr_, .len = len_})

#define core_array___core__clone__Clone_for__Array_T__N___20__clone( \
    len, src, dst, elem_type, _ret_t)                                \
  (memcpy(dst, src, len * sizeof(elem_type)))
#define TryFromSliceError uint8_t

#define Eurydice_array_eq(sz, a1, a2, t, _) \
  (memcmp(a1, a2, sz * sizeof(t)) == 0)
#define core_array_equality___core__cmp__PartialEq__Array_U__N___for__Array_T__N____eq( \
    sz, a1, a2, t, _, _ret_t)                                                           \
  Eurydice_array_eq(sz, a1, a2, t, _)
#define core_array_equality___core__cmp__PartialEq__0___Slice_U____for__Array_T__N___3__eq( \
    sz, a1, a2, t, _, _ret_t)                                                               \
  Eurydice_array_eq(sz, a1, ((a2)->ptr), t, _)

#define Eurydice_slice_split_at(slice, mid, element_type, ret_t) \
  (CLITERAL(ret_t){                                              \
      .fst = EURYDICE_SLICE((element_type *)slice.ptr, 0, mid),  \
      .snd = EURYDICE_SLICE((element_type *)slice.ptr, mid, slice.len)})
#define Eurydice_slice_split_at_mut(slice, mid, element_type, ret_t) \
  (CLITERAL(ret_t){                                                  \
      .fst = {.ptr = slice.ptr, .len = mid},                         \
      .snd = {.ptr = (char *)slice.ptr + mid * sizeof(element_type), \
              .len = slice.len - mid}})

// Conversion of slice to an array, rewritten (by Eurydice) to name the
// destination array, since arrays are not values in C.
// N.B.: see note in karamel/lib/Inlining.ml if you change this.
#define Eurydice_slice_to_array2(dst, src, _, t_arr)                      \
  Eurydice_slice_to_array3(&(dst)->tag, (char *)&(dst)->val.case_Ok, src, \
                           sizeof(t_arr))

static inline void Eurydice_slice_to_array3(uint8_t *dst_tag, char *dst_ok,
                                            Eurydice_slice src, size_t sz) {
  *dst_tag = 0;
  memcpy(dst_ok, src.ptr, sz);
}

// CORE STUFF (conversions, endianness, ...)

static inline void core_num__u64_9__to_le_bytes(uint64_t v, uint8_t buf[8]) {
  memcpy(buf, &v, sizeof(v));
}
static inline uint64_t core_num__u64_9__from_le_bytes(uint8_t buf[8]) {
  uint64_t v;
  memcpy(&v, buf, sizeof(v));
  return v;
}

static inline uint32_t core_num__u32_8__from_le_bytes(uint8_t buf[4]) {
  uint32_t v;
  memcpy(&v, buf, sizeof(v));
  return v;
}

static inline uint32_t core_num__u8_6__count_ones(uint8_t x0) {
#ifdef _MSC_VER
  return __popcnt(x0);
#else
  return __builtin_popcount(x0);
#endif
}

// unsigned overflow wraparound semantics in C
static inline uint16_t core_num__u16_7__wrapping_add(uint16_t x, uint16_t y) {
  return x + y;
}
static inline uint8_t core_num__u8_6__wrapping_sub(uint8_t x, uint8_t y) {
  return x - y;
}

// ITERATORS

#define Eurydice_range_iter_next(iter_ptr, t, ret_t) \
  (((iter_ptr)->start == (iter_ptr)->end)            \
       ? (CLITERAL(ret_t){.tag = None, .f0 = 0})     \
       : (CLITERAL(ret_t){.tag = Some, .f0 = (iter_ptr)->start++}))

#define core_iter_range___core__iter__traits__iterator__Iterator_for_core__ops__range__Range_A__TraitClause_0___6__next \
  Eurydice_range_iter_next

// See note in karamel/lib/Inlining.ml if you change this
#define Eurydice_into_iter(x, t, _ret_t) (x)
#define core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter \
  Eurydice_into_iter

#if defined(__cplusplus)
}
#endif
