/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 8db8a4838ea46c9ac681ba1051d1d296dd0d54b7
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8
 * Libcrux: d992e8bff91dab77b6f0abebf16384ce422b310c
 */

#ifndef __libcrux_sha3_libcrux_ml_kem_H
#define __libcrux_sha3_libcrux_ml_kem_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"

extern uint8_t libcrux_intrinsics_arm64_extract__vaddq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vaddq_u32(uint8_t x0,
                                                           uint8_t x1);

extern uint16_t libcrux_intrinsics_arm64_extract__vaddv_u16(uint8_t x0);

extern int16_t libcrux_intrinsics_arm64_extract__vaddvq_s16(uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vandq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vandq_u16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vandq_u32(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vbicq_u64(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vcgeq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vdupq_n_s16(int16_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vdupq_n_u16(uint16_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vdupq_n_u32(uint32_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vdupq_n_u64(uint64_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__veorq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__veorq_u64(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vget_high_u16(uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vget_low_s16(uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vget_low_u16(uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vld1q_bytes_u64(
    Eurydice_slice x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vld1q_s16(Eurydice_slice x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vld1q_u64(Eurydice_slice x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vld1q_u8(Eurydice_slice x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vmlal_high_s16(uint8_t x0,
                                                                uint8_t x1,
                                                                uint8_t x2);

extern uint8_t libcrux_intrinsics_arm64_extract__vmlal_s16(uint8_t x0,
                                                           uint8_t x1,
                                                           uint8_t x2);

extern uint8_t libcrux_intrinsics_arm64_extract__vmull_high_s16(uint8_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vmull_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vmulq_n_s16(uint8_t x0,
                                                             int16_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vmulq_n_u16(uint8_t x0,
                                                             uint16_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vmulq_n_u32(uint8_t x0,
                                                             uint32_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vmulq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vqdmulhq_n_s16(uint8_t x0,
                                                                int16_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vqdmulhq_n_s32(uint8_t x0,
                                                                int32_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vqdmulhq_s16(uint8_t x0,
                                                              uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vqtbl1q_u8(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s32(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s16_s64(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u32(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s16_u8(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s32_s16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s32_u32(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_s64_s32(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u16_s16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u16_u8(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u32_s32(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s16(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vreinterpretq_u8_s64(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_arm64_extract__vshlq_n_u32(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshlq_n_u64(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshlq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshlq_u16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshrq_n_s16(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshrq_n_u16(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshrq_n_u32(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vshrq_n_u64(int32_t x0,
                                                             uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vsliq_n_s32(int32_t x0,
                                                             uint8_t x1,
                                                             uint8_t x2);

extern uint8_t libcrux_intrinsics_arm64_extract__vsliq_n_s64(int32_t x0,
                                                             uint8_t x1,
                                                             uint8_t x2);

extern void libcrux_intrinsics_arm64_extract__vst1q_bytes_u64(Eurydice_slice x0,
                                                              uint8_t x1);

extern void libcrux_intrinsics_arm64_extract__vst1q_s16(Eurydice_slice x0,
                                                        uint8_t x1);

extern void libcrux_intrinsics_arm64_extract__vst1q_u8(Eurydice_slice x0,
                                                       uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vsubq_s16(uint8_t x0,
                                                           uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn1q_s16(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn1q_s32(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn1q_s64(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn1q_u64(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn2q_s16(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn2q_s32(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn2q_s64(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_arm64_extract__vtrn2q_u64(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_add_epi16(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_add_epi32(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_and_si256(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_blend_epi16(int32_t x0,
                                                                 uint8_t x1,
                                                                 uint8_t x2);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_castsi128_si256(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_castsi256_si128(
    uint8_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_cmpgt_epi16(uint8_t x0,
                                                                 uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_cvtepi16_epi32(uint8_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_extracti128_si256(
    int32_t x0, uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_inserti128_si256(
    int32_t x0, uint8_t x1, uint8_t x2);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_loadu_si256_i16(
    Eurydice_slice x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_madd_epi16(uint8_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_mul_epu32(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_mulhi_epi16(uint8_t x0,
                                                                 uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_mullo_epi16(uint8_t x0,
                                                                 uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_mullo_epi32(uint8_t x0,
                                                                 uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_packs_epi32(uint8_t x0,
                                                                 uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_permute4x64_epi64(
    int32_t x0, uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_permutevar8x32_epi32(
    uint8_t x0, uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_set1_epi16(int16_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_set1_epi32(int32_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_set_epi16(
    int16_t x0, int16_t x1, int16_t x2, int16_t x3, int16_t x4, int16_t x5,
    int16_t x6, int16_t x7, int16_t x8, int16_t x9, int16_t x10, int16_t x11,
    int16_t x12, int16_t x13, int16_t x14, int16_t x15);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_set_epi32(
    int32_t x0, int32_t x1, int32_t x2, int32_t x3, int32_t x4, int32_t x5,
    int32_t x6, int32_t x7);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_set_epi8(
    int8_t x0, int8_t x1, int8_t x2, int8_t x3, int8_t x4, int8_t x5, int8_t x6,
    int8_t x7, int8_t x8, int8_t x9, int8_t x10, int8_t x11, int8_t x12,
    int8_t x13, int8_t x14, int8_t x15, int8_t x16, int8_t x17, int8_t x18,
    int8_t x19, int8_t x20, int8_t x21, int8_t x22, int8_t x23, int8_t x24,
    int8_t x25, int8_t x26, int8_t x27, int8_t x28, int8_t x29, int8_t x30,
    int8_t x31);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_setzero_si256(void);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_shuffle_epi32(int32_t x0,
                                                                   uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_shuffle_epi8(uint8_t x0,
                                                                  uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_slli_epi16(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_slli_epi32(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_sllv_epi32(uint8_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_srai_epi16(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_srai_epi32(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_srli_epi16(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_srli_epi32(int32_t x0,
                                                                uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_srli_epi64(int32_t x0,
                                                                uint8_t x1);

extern void libcrux_intrinsics_avx2_extract_mm256_storeu_si256_i16(
    Eurydice_slice x0, uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_sub_epi16(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_unpackhi_epi32(uint8_t x0,
                                                                    uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_unpackhi_epi64(uint8_t x0,
                                                                    uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_unpacklo_epi32(uint8_t x0,
                                                                    uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm256_xor_si256(uint8_t x0,
                                                               uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_add_epi16(uint8_t x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_loadu_si128(
    Eurydice_slice x0);

extern int32_t libcrux_intrinsics_avx2_extract_mm_movemask_epi8(uint8_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_mulhi_epi16(uint8_t x0,
                                                              uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_mullo_epi16(uint8_t x0,
                                                              uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_packs_epi16(uint8_t x0,
                                                              uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_set1_epi16(int16_t x0);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_set_epi8(
    uint8_t x0, uint8_t x1, uint8_t x2, uint8_t x3, uint8_t x4, uint8_t x5,
    uint8_t x6, uint8_t x7, uint8_t x8, uint8_t x9, uint8_t x10, uint8_t x11,
    uint8_t x12, uint8_t x13, uint8_t x14, uint8_t x15);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_shuffle_epi8(uint8_t x0,
                                                               uint8_t x1);

extern void libcrux_intrinsics_avx2_extract_mm_storeu_bytes_si128(
    Eurydice_slice x0, uint8_t x1);

extern void libcrux_intrinsics_avx2_extract_mm_storeu_si128(Eurydice_slice x0,
                                                            uint8_t x1);

extern uint8_t libcrux_intrinsics_avx2_extract_mm_sub_epi16(uint8_t x0,
                                                            uint8_t x1);

#if defined(__cplusplus)
}
#endif

#define __libcrux_sha3_libcrux_ml_kem_H_DEFINED
#endif
