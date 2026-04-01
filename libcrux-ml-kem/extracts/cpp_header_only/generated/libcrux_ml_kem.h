/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 377317d6b25702c46ffff072fa00a3e32095e46f
 * Eurydice: b227478b67c6a6e2ff611f978f10d6b7f26472ac
 * Karamel: 4e64d915da3c172d1dfad805b8e1a46beff938bc
 * F*: 89901492c020c74b82d811d27f3149c222d9b8b5
 * Libcrux: a53e03cfd7b424560bdfefc9d483f87faacd3122
 */

#ifndef libcrux_ml_kem_H
#define libcrux_ml_kem_H

#include "eurydice_glue.h"
#include "libcrux_mlkem_core.h"

typedef __m128i libcrux_intrinsics_avx2_Vec128;

typedef __m256i libcrux_intrinsics_avx2_Vec256;

typedef __m256 libcrux_intrinsics_avx2_Vec256Float;

extern __m256i libcrux_intrinsics_avx2_mm256_abs_epi32(__m256i x0);

extern __m256i libcrux_intrinsics_avx2_mm256_add_epi16(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_add_epi32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_add_epi64(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_and_si256(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_andnot_si256(__m256i x0,
                                                          __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_blend_epi16(int32_t x0, __m256i x1,
                                                         __m256i x2);

extern __m256i libcrux_intrinsics_avx2_mm256_blend_epi32(int32_t x0, __m256i x1,
                                                         __m256i x2);

extern __m256i libcrux_intrinsics_avx2_mm256_bsrli_epi128(int32_t x0,
                                                          __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_castps_si256(__m256 x0);

extern __m256i libcrux_intrinsics_avx2_mm256_castsi128_si256(__m128i x0);

extern __m256 libcrux_intrinsics_avx2_mm256_castsi256_ps(__m256i x0);

extern __m128i libcrux_intrinsics_avx2_mm256_castsi256_si128(__m256i x0);

extern __m256i libcrux_intrinsics_avx2_mm256_cmpeq_epi32(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_cmpgt_epi16(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_cmpgt_epi32(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_cvtepi16_epi32(__m128i x0);

extern __m128i libcrux_intrinsics_avx2_mm256_extracti128_si256(int32_t x0,
                                                               __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_inserti128_si256(int32_t x0,
                                                              __m256i x1,
                                                              __m128i x2);

extern __m256i libcrux_intrinsics_avx2_mm256_loadu_si256_i16(
    Eurydice_borrow_slice_i16 x0);

extern __m256i libcrux_intrinsics_avx2_mm256_loadu_si256_i32(
    Eurydice_dst_ref_shared_fc x0);

extern __m256i libcrux_intrinsics_avx2_mm256_loadu_si256_u8(
    Eurydice_borrow_slice_u8 x0);

extern __m256i libcrux_intrinsics_avx2_mm256_madd_epi16(__m256i x0, __m256i x1);

extern int32_t libcrux_intrinsics_avx2_mm256_movemask_ps(__m256 x0);

extern __m256i libcrux_intrinsics_avx2_mm256_mul_epi32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_mul_epu32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_mulhi_epi16(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_mullo_epi16(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_mullo_epi32(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_or_si256(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_packs_epi32(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_permute2x128_si256(int32_t x0,
                                                                __m256i x1,
                                                                __m256i x2);

extern __m256i libcrux_intrinsics_avx2_mm256_permute4x64_epi64(int32_t x0,
                                                               __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_permutevar8x32_epi32(__m256i x0,
                                                                  __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_set1_epi16(int16_t x0);

extern __m256i libcrux_intrinsics_avx2_mm256_set1_epi32(int32_t x0);

extern __m256i libcrux_intrinsics_avx2_mm256_set1_epi64x(int64_t x0);

extern __m256i libcrux_intrinsics_avx2_mm256_set_epi16(
    int16_t x0, int16_t x1, int16_t x2, int16_t x3, int16_t x4, int16_t x5,
    int16_t x6, int16_t x7, int16_t x8, int16_t x9, int16_t x10, int16_t x11,
    int16_t x12, int16_t x13, int16_t x14, int16_t x15);

extern __m256i libcrux_intrinsics_avx2_mm256_set_epi32(int32_t x0, int32_t x1,
                                                       int32_t x2, int32_t x3,
                                                       int32_t x4, int32_t x5,
                                                       int32_t x6, int32_t x7);

extern __m256i libcrux_intrinsics_avx2_mm256_set_epi64x(int64_t x0, int64_t x1,
                                                        int64_t x2, int64_t x3);

extern __m256i libcrux_intrinsics_avx2_mm256_set_epi8(
    int8_t x0, int8_t x1, int8_t x2, int8_t x3, int8_t x4, int8_t x5, int8_t x6,
    int8_t x7, int8_t x8, int8_t x9, int8_t x10, int8_t x11, int8_t x12,
    int8_t x13, int8_t x14, int8_t x15, int8_t x16, int8_t x17, int8_t x18,
    int8_t x19, int8_t x20, int8_t x21, int8_t x22, int8_t x23, int8_t x24,
    int8_t x25, int8_t x26, int8_t x27, int8_t x28, int8_t x29, int8_t x30,
    int8_t x31);

extern __m256i libcrux_intrinsics_avx2_mm256_set_m128i(__m128i x0, __m128i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_setzero_si256(void);

extern __m256i libcrux_intrinsics_avx2_mm256_shuffle_epi32(int32_t x0,
                                                           __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_shuffle_epi8(__m256i x0,
                                                          __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_sign_epi32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_slli_epi16(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_slli_epi32(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_slli_epi64(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_sllv_epi32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srai_epi16(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srai_epi32(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srli_epi16(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srli_epi32(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srli_epi64(int32_t x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srlv_epi32(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_srlv_epi64(__m256i x0, __m256i x1);

extern void libcrux_intrinsics_avx2_mm256_storeu_si256_i16(
    Eurydice_mut_borrow_slice_i16 x0, __m256i x1);

extern void libcrux_intrinsics_avx2_mm256_storeu_si256_i32(
    Eurydice_dst_ref_mut_fc x0, __m256i x1);

extern void libcrux_intrinsics_avx2_mm256_storeu_si256_u8(
    Eurydice_mut_borrow_slice_u8 x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_sub_epi16(__m256i x0, __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_sub_epi32(__m256i x0, __m256i x1);

extern int32_t libcrux_intrinsics_avx2_mm256_testz_si256(__m256i x0,
                                                         __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_unpackhi_epi32(__m256i x0,
                                                            __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_unpackhi_epi64(__m256i x0,
                                                            __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_unpacklo_epi32(__m256i x0,
                                                            __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_unpacklo_epi64(__m256i x0,
                                                            __m256i x1);

extern __m256i libcrux_intrinsics_avx2_mm256_xor_si256(__m256i x0, __m256i x1);

extern __m128i libcrux_intrinsics_avx2_mm_add_epi16(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_aesenc_si128(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_aesenclast_si128(__m128i x0,
                                                           __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_aeskeygenassist_si128(int32_t x0,
                                                                __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_clmulepi64_si128(int32_t x0,
                                                           __m128i x1,
                                                           __m128i x2);

extern __m128i libcrux_intrinsics_avx2_mm_loadu_si128(
    Eurydice_borrow_slice_u8 x0);

extern __m128i libcrux_intrinsics_avx2_mm_loadu_si128_u128(
    const Eurydice_Int128_uint128_t *x0);

extern int32_t libcrux_intrinsics_avx2_mm_movemask_epi8(__m128i x0);

extern __m128i libcrux_intrinsics_avx2_mm_mulhi_epi16(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_mullo_epi16(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_packs_epi16(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_set1_epi16(int16_t x0);

extern __m128i libcrux_intrinsics_avx2_mm_set_epi32(int32_t x0, int32_t x1,
                                                    int32_t x2, int32_t x3);

extern __m128i libcrux_intrinsics_avx2_mm_set_epi8(
    int8_t x0, int8_t x1, int8_t x2, int8_t x3, int8_t x4, int8_t x5, int8_t x6,
    int8_t x7, int8_t x8, int8_t x9, int8_t x10, int8_t x11, int8_t x12,
    int8_t x13, int8_t x14, int8_t x15);

extern __m128i libcrux_intrinsics_avx2_mm_setzero_si128(void);

extern __m128i libcrux_intrinsics_avx2_mm_shuffle_epi32(int32_t x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_shuffle_epi8(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_slli_si128(int32_t x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_sllv_epi32(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_srli_epi64(int32_t x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_srli_si128(int32_t x0, __m128i x1);

extern void libcrux_intrinsics_avx2_mm_storeu_bytes_si128(
    Eurydice_mut_borrow_slice_u8 x0, __m128i x1);

extern void libcrux_intrinsics_avx2_mm_storeu_si128(
    Eurydice_mut_borrow_slice_i16 x0, __m128i x1);

extern void libcrux_intrinsics_avx2_mm_storeu_si128_i32(
    Eurydice_dst_ref_mut_fc x0, __m128i x1);

extern void libcrux_intrinsics_avx2_mm_storeu_si128_u128(
    Eurydice_Int128_uint128_t *x0, __m128i x1);

extern void libcrux_intrinsics_avx2_mm_storeu_si128_u8(
    Eurydice_mut_borrow_slice_u8 x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_sub_epi16(__m128i x0, __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_unpackhi_epi64(__m128i x0,
                                                         __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_unpacklo_epi64(__m128i x0,
                                                         __m128i x1);

extern __m128i libcrux_intrinsics_avx2_mm_xor_si128(__m128i x0, __m128i x1);

extern __m256i libcrux_intrinsics_avx2_vec256_blendv_epi32(__m256i x0,
                                                           __m256i x1,
                                                           __m256i x2);

#define libcrux_ml_kem_H_DEFINED
#endif /* libcrux_ml_kem_H */
