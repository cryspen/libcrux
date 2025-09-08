/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 667d2fc98984ff7f3df989c2367e6c1fa4a000e7
 * Eurydice: 564ce891b07fd4aefe7d5ccd78e61400b4ac4a2b
 * Karamel: 06a6d2fb3a547d11c9f6dbec26f1f9b5e0dbf411
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#ifndef libcrux_mlkem_avx2_H
#define libcrux_mlkem_avx2_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_core.h"

libcrux_sha3_Sha3_512Digest libcrux_ml_kem_hash_functions_avx2_G(
    Eurydice_slice input);

Eurydice_arr_60 libcrux_ml_kem_hash_functions_avx2_H(Eurydice_slice input);

__m256i libcrux_ml_kem_vector_avx2_vec_zero(void);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_ZERO_f5(void);

__m256i libcrux_ml_kem_vector_avx2_vec_from_i16_array(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_from_i16_array_f5(Eurydice_slice array);

Eurydice_arr_e2 libcrux_ml_kem_vector_avx2_vec_to_i16_array(__m256i v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_avx2_to_i16_array_f5(__m256i x);

__m256i libcrux_ml_kem_vector_avx2_from_bytes(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_from_bytes_f5(Eurydice_slice array);

void libcrux_ml_kem_vector_avx2_to_bytes(__m256i x, Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
void libcrux_ml_kem_vector_avx2_to_bytes_f5(__m256i x, Eurydice_slice bytes);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_add(__m256i lhs, __m256i rhs);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_add_f5(__m256i lhs, __m256i *rhs);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_sub(__m256i lhs, __m256i rhs);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_sub_f5(__m256i lhs, __m256i *rhs);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_multiply_by_constant(
    __m256i vector, int16_t constant);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_multiply_by_constant_f5(__m256i vec,
                                                           int16_t c);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_cond_subtract_3329(
    __m256i vector);

__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_cond_subtract_3329_f5(__m256i vector);

#define LIBCRUX_ML_KEM_VECTOR_AVX2_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

/**
 See Section 3.2 of the implementation notes document for an explanation
 of this code.
*/
__m256i libcrux_ml_kem_vector_avx2_arithmetic_barrett_reduce(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_barrett_reduce_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constant(
    __m256i vector, int16_t constant);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_montgomery_multiply_by_constant_f5(
    __m256i vector, int16_t constant);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_bitwise_and_with_constant(
    __m256i vector, int16_t constant);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_to_unsigned_representative(
    __m256i a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_to_unsigned_representative_f5(__m256i a);

__m256i libcrux_ml_kem_vector_avx2_compress_compress_message_coefficient(
    __m256i vector);

__m256i libcrux_ml_kem_vector_avx2_compress_1(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_compress_1_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_compress_mulhi_mm256_epi32(__m256i lhs,
                                                              __m256i rhs);

__m256i libcrux_ml_kem_vector_avx2_compress_decompress_1(__m256i a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_decompress_1_f5(__m256i a);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_by_constants(
    __m256i vec, __m256i constants);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_1_step_f5(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_2_step(__m256i vector,
                                                        int16_t zeta0,
                                                        int16_t zeta1);

__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step(__m256i vector,
                                                    int16_t zeta0,
                                                    int16_t zeta1);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_2_step_f5(__m256i vector,
                                                       int16_t zeta0,
                                                       int16_t zeta1);

__m128i
libcrux_ml_kem_vector_avx2_arithmetic_montgomery_multiply_m128i_by_constants(
    __m128i vec, __m128i constants);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_layer_3_step(__m256i vector,
                                                        int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step(__m256i vector,
                                                    int16_t zeta);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_layer_3_step_f5(__m256i vector,
                                                       int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_1_step_f5(
    __m256i vector, int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_2_step(__m256i vector,
                                                            int16_t zeta0,
                                                            int16_t zeta1);

__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step(__m256i vector,
                                                        int16_t zeta0,
                                                        int16_t zeta1);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_2_step_f5(__m256i vector,
                                                           int16_t zeta0,
                                                           int16_t zeta1);

__m256i libcrux_ml_kem_vector_avx2_ntt_inv_ntt_layer_3_step(__m256i vector,
                                                            int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step(__m256i vector,
                                                        int16_t zeta);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_inv_ntt_layer_3_step_f5(__m256i vector,
                                                           int16_t zeta);

__m256i libcrux_ml_kem_vector_avx2_arithmetic_montgomery_reduce_i32s(
    __m256i vec);

__m256i libcrux_ml_kem_vector_avx2_ntt_ntt_multiply(__m256i lhs, __m256i rhs,
                                                    int16_t zeta0,
                                                    int16_t zeta1,
                                                    int16_t zeta2,
                                                    int16_t zeta3);

__m256i libcrux_ml_kem_vector_avx2_ntt_multiply(__m256i *lhs, __m256i *rhs,
                                                int16_t zeta0, int16_t zeta1,
                                                int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_ntt_multiply_f5(__m256i *lhs, __m256i *rhs,
                                                   int16_t zeta0, int16_t zeta1,
                                                   int16_t zeta2,
                                                   int16_t zeta3);

Eurydice_arr_8b libcrux_ml_kem_vector_avx2_serialize_serialize_1(
    __m256i vector);

Eurydice_arr_8b libcrux_ml_kem_vector_avx2_serialize_1(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_8b libcrux_ml_kem_vector_avx2_serialize_1_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_i16s(
    int16_t a, int16_t b);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_1_deserialize_1_u8s(
    uint8_t a, uint8_t b);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_1(
    Eurydice_slice bytes);

__m256i libcrux_ml_kem_vector_avx2_deserialize_1(Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_1_f5(Eurydice_slice bytes);

/**
 `mm256_concat_pairs_n(n, x)` is then a sequence of 32 bits packets
 of the shape `0b0…0b₁…bₙa₁…aₙ`, if `x` is a sequence of pairs of
 16 bits, of the shape `(0b0…0a₁…aₙ, 0b0…0b₁…bₙ)` (where the last
 `n` bits are non-zero).
*/
__m256i libcrux_ml_kem_vector_avx2_serialize_mm256_concat_pairs_n(uint8_t n,
                                                                  __m256i x);

Eurydice_arr_c4 libcrux_ml_kem_vector_avx2_serialize_serialize_4(
    __m256i vector);

Eurydice_arr_c4 libcrux_ml_kem_vector_avx2_serialize_4(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_c4 libcrux_ml_kem_vector_avx2_serialize_4_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_i16s(
    int16_t b0, int16_t b1, int16_t b2, int16_t b3, int16_t b4, int16_t b5,
    int16_t b6, int16_t b7);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_4_deserialize_4_u8s(
    uint8_t b0, uint8_t b1, uint8_t b2, uint8_t b3, uint8_t b4, uint8_t b5,
    uint8_t b6, uint8_t b7);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_4(
    Eurydice_slice bytes);

__m256i libcrux_ml_kem_vector_avx2_deserialize_4(Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_4_f5(Eurydice_slice bytes);

Eurydice_arr_77 libcrux_ml_kem_vector_avx2_serialize_serialize_5(
    __m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_77 libcrux_ml_kem_vector_avx2_serialize_5_f5(__m256i vector);

/**
 We cannot model `mm256_inserti128_si256` on its own: it produces a
 Vec256 where the upper 128 bits are undefined. Thus
 `mm256_inserti128_si256` is not pure.

 Luckily, we always call `mm256_castsi128_si256` right after
 `mm256_inserti128_si256`: this composition sets the upper bits,
 making the whole computation pure again.
*/
__m256i libcrux_ml_kem_vector_avx2_serialize_mm256_si256_from_two_si128(
    __m128i lower, __m128i upper);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_5(
    Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_5_f5(Eurydice_slice bytes);

typedef struct core_core_arch_x86___m128i_x2_s {
  __m128i fst;
  __m128i snd;
} core_core_arch_x86___m128i_x2;

core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_10_serialize_10_vec(
    __m256i vector);

Eurydice_arr_dc libcrux_ml_kem_vector_avx2_serialize_serialize_10(
    __m256i vector);

Eurydice_arr_dc libcrux_ml_kem_vector_avx2_serialize_10(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_dc libcrux_ml_kem_vector_avx2_serialize_10_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_10_deserialize_10_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_10(
    Eurydice_slice bytes);

__m256i libcrux_ml_kem_vector_avx2_deserialize_10(Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_10_f5(Eurydice_slice bytes);

Eurydice_arr_f3 libcrux_ml_kem_vector_avx2_serialize_serialize_11(
    __m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_f3 libcrux_ml_kem_vector_avx2_serialize_11_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_11(
    Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_11_f5(Eurydice_slice bytes);

core_core_arch_x86___m128i_x2
libcrux_ml_kem_vector_avx2_serialize_serialize_12_serialize_12_vec(
    __m256i vector);

Eurydice_arr_6d libcrux_ml_kem_vector_avx2_serialize_serialize_12(
    __m256i vector);

Eurydice_arr_6d libcrux_ml_kem_vector_avx2_serialize_12(__m256i vector);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
Eurydice_arr_6d libcrux_ml_kem_vector_avx2_serialize_12_f5(__m256i vector);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_12_deserialize_12_vec(
    __m128i lower_coefficients0, __m128i upper_coefficients0);

__m256i libcrux_ml_kem_vector_avx2_serialize_deserialize_12(
    Eurydice_slice bytes);

__m256i libcrux_ml_kem_vector_avx2_deserialize_12(Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_deserialize_12_f5(Eurydice_slice bytes);

size_t libcrux_ml_kem_vector_avx2_sampling_rejection_sample(
    Eurydice_slice input, Eurydice_slice output);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
size_t libcrux_ml_kem_vector_avx2_rej_sample_f5(Eurydice_slice input,
                                                Eurydice_slice output);

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::vector::avx2::SIMD256Vector}
*/
__m256i libcrux_ml_kem_vector_avx2_clone_fd(__m256i *self);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem_avx2_H_DEFINED
#endif /* libcrux_mlkem_avx2_H */
