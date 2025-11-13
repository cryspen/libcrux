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

#ifndef libcrux_intrinsics_x86_H
#define libcrux_intrinsics_x86_H

#include "eurydice_glue.h"

#define core_core_arch_x86_avx512f__mm256_i32scatter_epi32(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i32scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i32scatter_epi32_(int32_t x0,
                                                                int32_t *x1,
                                                                __m256i x2,
                                                                __m256i x3);

#define core_core_arch_x86_avx512f__mm256_i32scatter_epi64(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i32scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i32scatter_epi64_(int32_t x0,
                                                                int64_t *x1,
                                                                __m128i x2,
                                                                __m256i x3);

#define core_core_arch_x86_avx512f__mm256_i32scatter_pd(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i32scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i32scatter_pd_(int32_t x0,
                                                             float64_t *x1,
                                                             __m128i x2,
                                                             __m256d x3);

#define core_core_arch_x86_avx512f__mm256_i32scatter_ps(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i32scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i32scatter_ps_(int32_t x0,
                                                             float32_t *x1,
                                                             __m256i x2,
                                                             __m256 x3);

#define core_core_arch_x86_avx512f__mm256_i64scatter_epi32(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i64scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i64scatter_epi32_(int32_t x0,
                                                                int32_t *x1,
                                                                __m256i x2,
                                                                __m128i x3);

#define core_core_arch_x86_avx512f__mm256_i64scatter_epi64(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i64scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i64scatter_epi64_(int32_t x0,
                                                                int64_t *x1,
                                                                __m256i x2,
                                                                __m256i x3);

#define core_core_arch_x86_avx512f__mm256_i64scatter_pd(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i64scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i64scatter_pd_(int32_t x0,
                                                             float64_t *x1,
                                                             __m256i x2,
                                                             __m256d x3);

#define core_core_arch_x86_avx512f__mm256_i64scatter_ps(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm256_i64scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm256_i64scatter_ps_(int32_t x0,
                                                             float32_t *x1,
                                                             __m256i x2,
                                                             __m128 x3);

#define core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi32(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi32_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi32_(
    int32_t x0, int32_t *x1, uint8_t x2, __m256i x3, __m256i x4);

#define core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi64(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi64_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i32scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m128i x3, __m256i x4);

#define core_core_arch_x86_avx512f__mm256_mask_i32scatter_pd(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm256_mask_i32scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i32scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m128i x3, __m256d x4);

#define core_core_arch_x86_avx512f__mm256_mask_i32scatter_ps(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm256_mask_i32scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i32scatter_ps_(
    int32_t x0, float32_t *x1, uint8_t x2, __m256i x3, __m256 x4);

#define core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi32(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi32_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi32_(
    int32_t x0, int32_t *x1, uint8_t x2, __m256i x3, __m128i x4);

#define core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi64(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi64_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i64scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m256i x3, __m256i x4);

#define core_core_arch_x86_avx512f__mm256_mask_i64scatter_pd(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm256_mask_i64scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i64scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m256i x3, __m256d x4);

#define core_core_arch_x86_avx512f__mm256_mask_i64scatter_ps(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm256_mask_i64scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm256_mask_i64scatter_ps_(
    int32_t x0, float32_t *x1, uint8_t x2, __m256i x3, __m128 x4);

#define core_core_arch_x86_avx512f__mm512_i32loscatter_epi64(x_0, x_1, x_2, \
                                                             x_3, _ret_t)   \
  core_core_arch_x86_avx512f__mm512_i32loscatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32loscatter_epi64_(int32_t x0,
                                                                  int64_t *x1,
                                                                  __m512i x2,
                                                                  __m512i x3);

#define core_core_arch_x86_avx512f__mm512_i32loscatter_pd(x_0, x_1, x_2, x_3, \
                                                          _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i32loscatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32loscatter_pd_(int32_t x0,
                                                               float64_t *x1,
                                                               __m512i x2,
                                                               __m512d x3);

#define core_core_arch_x86_avx512f__mm512_i32scatter_epi32(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i32scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32scatter_epi32_(int32_t x0,
                                                                int32_t *x1,
                                                                __m512i x2,
                                                                __m512i x3);

#define core_core_arch_x86_avx512f__mm512_i32scatter_epi64(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i32scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32scatter_epi64_(int32_t x0,
                                                                int64_t *x1,
                                                                __m256i x2,
                                                                __m512i x3);

#define core_core_arch_x86_avx512f__mm512_i32scatter_pd(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i32scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32scatter_pd_(int32_t x0,
                                                             float64_t *x1,
                                                             __m256i x2,
                                                             __m512d x3);

#define core_core_arch_x86_avx512f__mm512_i32scatter_ps(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i32scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i32scatter_ps_(int32_t x0,
                                                             float32_t *x1,
                                                             __m512i x2,
                                                             __m512 x3);

#define core_core_arch_x86_avx512f__mm512_i64scatter_epi32(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i64scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i64scatter_epi32_(int32_t x0,
                                                                int32_t *x1,
                                                                __m512i x2,
                                                                __m256i x3);

#define core_core_arch_x86_avx512f__mm512_i64scatter_epi64(x_0, x_1, x_2, x_3, \
                                                           _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i64scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i64scatter_epi64_(int32_t x0,
                                                                int64_t *x1,
                                                                __m512i x2,
                                                                __m512i x3);

#define core_core_arch_x86_avx512f__mm512_i64scatter_pd(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i64scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i64scatter_pd_(int32_t x0,
                                                             float64_t *x1,
                                                             __m512i x2,
                                                             __m512d x3);

#define core_core_arch_x86_avx512f__mm512_i64scatter_ps(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm512_i64scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm512_i64scatter_ps_(int32_t x0,
                                                             float32_t *x1,
                                                             __m512i x2,
                                                             __m256 x3);

#define core_core_arch_x86_avx512f__mm512_mask_i32loscatter_epi64(          \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                        \
  core_core_arch_x86_avx512f__mm512_mask_i32loscatter_epi64_(x_0, x_1, x_2, \
                                                             x_3, x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32loscatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m512i x3, __m512i x4);

#define core_core_arch_x86_avx512f__mm512_mask_i32loscatter_pd(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                          \
  core_core_arch_x86_avx512f__mm512_mask_i32loscatter_pd_(x_0, x_1, x_2, x_3, \
                                                          x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32loscatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m512i x3, __m512d x4);

#define core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi32(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi32_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi32_(
    int32_t x0, int32_t *x1, uint16_t x2, __m512i x3, __m512i x4);

#define core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi64(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi64_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m256i x3, __m512i x4);

#define core_core_arch_x86_avx512f__mm512_mask_i32scatter_pd(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm512_mask_i32scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m256i x3, __m512d x4);

#define core_core_arch_x86_avx512f__mm512_mask_i32scatter_ps(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm512_mask_i32scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i32scatter_ps_(
    int32_t x0, float32_t *x1, uint16_t x2, __m512i x3, __m512 x4);

#define core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi32(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi32_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi32_(
    int32_t x0, int32_t *x1, uint8_t x2, __m512i x3, __m256i x4);

#define core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi64(               \
    x_0, x_1, x_2, x_3, x_4, _ret_t)                                           \
  core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi64_(x_0, x_1, x_2, x_3, \
                                                           x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i64scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m512i x3, __m512i x4);

#define core_core_arch_x86_avx512f__mm512_mask_i64scatter_pd(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm512_mask_i64scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i64scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m512i x3, __m512d x4);

#define core_core_arch_x86_avx512f__mm512_mask_i64scatter_ps(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm512_mask_i64scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm512_mask_i64scatter_ps_(
    int32_t x0, float32_t *x1, uint8_t x2, __m512i x3, __m256 x4);

#define core_core_arch_x86_avx512f__mm_i32scatter_epi32(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm_i32scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i32scatter_epi32_(int32_t x0,
                                                             int32_t *x1,
                                                             __m128i x2,
                                                             __m128i x3);

#define core_core_arch_x86_avx512f__mm_i32scatter_epi64(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm_i32scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i32scatter_epi64_(int32_t x0,
                                                             int64_t *x1,
                                                             __m128i x2,
                                                             __m128i x3);

#define core_core_arch_x86_avx512f__mm_i32scatter_pd(x_0, x_1, x_2, x_3, \
                                                     _ret_t)             \
  core_core_arch_x86_avx512f__mm_i32scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i32scatter_pd_(int32_t x0,
                                                          float64_t *x1,
                                                          __m128i x2,
                                                          __m128d x3);

#define core_core_arch_x86_avx512f__mm_i32scatter_ps(x_0, x_1, x_2, x_3, \
                                                     _ret_t)             \
  core_core_arch_x86_avx512f__mm_i32scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i32scatter_ps_(int32_t x0,
                                                          float32_t *x1,
                                                          __m128i x2,
                                                          __m128 x3);

#define core_core_arch_x86_avx512f__mm_i64scatter_epi32(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm_i64scatter_epi32_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i64scatter_epi32_(int32_t x0,
                                                             int32_t *x1,
                                                             __m128i x2,
                                                             __m128i x3);

#define core_core_arch_x86_avx512f__mm_i64scatter_epi64(x_0, x_1, x_2, x_3, \
                                                        _ret_t)             \
  core_core_arch_x86_avx512f__mm_i64scatter_epi64_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i64scatter_epi64_(int32_t x0,
                                                             int64_t *x1,
                                                             __m128i x2,
                                                             __m128i x3);

#define core_core_arch_x86_avx512f__mm_i64scatter_pd(x_0, x_1, x_2, x_3, \
                                                     _ret_t)             \
  core_core_arch_x86_avx512f__mm_i64scatter_pd_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i64scatter_pd_(int32_t x0,
                                                          float64_t *x1,
                                                          __m128i x2,
                                                          __m128d x3);

#define core_core_arch_x86_avx512f__mm_i64scatter_ps(x_0, x_1, x_2, x_3, \
                                                     _ret_t)             \
  core_core_arch_x86_avx512f__mm_i64scatter_ps_(x_0, x_1, x_2, x_3)

extern void core_core_arch_x86_avx512f__mm_i64scatter_ps_(int32_t x0,
                                                          float32_t *x1,
                                                          __m128i x2,
                                                          __m128 x3);

#define core_core_arch_x86_avx512f__mm_mask_i32scatter_epi32(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm_mask_i32scatter_epi32_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i32scatter_epi32_(
    int32_t x0, int32_t *x1, uint8_t x2, __m128i x3, __m128i x4);

#define core_core_arch_x86_avx512f__mm_mask_i32scatter_epi64(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm_mask_i32scatter_epi64_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i32scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m128i x3, __m128i x4);

#define core_core_arch_x86_avx512f__mm_mask_i32scatter_pd(x_0, x_1, x_2, x_3, \
                                                          x_4, _ret_t)        \
  core_core_arch_x86_avx512f__mm_mask_i32scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i32scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m128i x3, __m128d x4);

#define core_core_arch_x86_avx512f__mm_mask_i32scatter_ps(x_0, x_1, x_2, x_3, \
                                                          x_4, _ret_t)        \
  core_core_arch_x86_avx512f__mm_mask_i32scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i32scatter_ps_(
    int32_t x0, float32_t *x1, uint8_t x2, __m128i x3, __m128 x4);

#define core_core_arch_x86_avx512f__mm_mask_i64scatter_epi32(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm_mask_i64scatter_epi32_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i64scatter_epi32_(
    int32_t x0, int32_t *x1, uint8_t x2, __m128i x3, __m128i x4);

#define core_core_arch_x86_avx512f__mm_mask_i64scatter_epi64(x_0, x_1, x_2,    \
                                                             x_3, x_4, _ret_t) \
  core_core_arch_x86_avx512f__mm_mask_i64scatter_epi64_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i64scatter_epi64_(
    int32_t x0, int64_t *x1, uint8_t x2, __m128i x3, __m128i x4);

#define core_core_arch_x86_avx512f__mm_mask_i64scatter_pd(x_0, x_1, x_2, x_3, \
                                                          x_4, _ret_t)        \
  core_core_arch_x86_avx512f__mm_mask_i64scatter_pd_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i64scatter_pd_(
    int32_t x0, float64_t *x1, uint8_t x2, __m128i x3, __m128d x4);

#define core_core_arch_x86_avx512f__mm_mask_i64scatter_ps(x_0, x_1, x_2, x_3, \
                                                          x_4, _ret_t)        \
  core_core_arch_x86_avx512f__mm_mask_i64scatter_ps_(x_0, x_1, x_2, x_3, x_4)

extern void core_core_arch_x86_avx512f__mm_mask_i64scatter_ps_(
    int32_t x0, float32_t *x1, uint8_t x2, __m128i x3, __m128 x4);

typedef struct uint32_t_x2_s {
  uint32_t fst;
  uint32_t snd;
} uint32_t_x2;

#define core_core_arch_x86_rtm__xabort(x_0, _ret_t) \
  core_core_arch_x86_rtm__xabort_(x_0)

extern void core_core_arch_x86_rtm__xabort_(uint32_t x0);

#define core_core_arch_x86_sse__mm_prefetch(x_0, x_1, _ret_t) \
  core_core_arch_x86_sse__mm_prefetch_(x_0, x_1)

extern void core_core_arch_x86_sse__mm_prefetch_(int32_t x0, int8_t *x1);

#define libcrux_intrinsics_x86_H_DEFINED
#endif /* libcrux_intrinsics_x86_H */
