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


#ifndef libcrux_mlkem_neon_H
#define libcrux_mlkem_neon_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "intrinsics/libcrux_intrinsics_arm64.h"

#include "libcrux_core.h"

libcrux_sha3_Sha3_512Digest libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input);

Eurydice_arr_60 libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input);

typedef struct libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_s
{
  int16x8_t low;
  int16x8_t high;
}
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector;

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_ZERO(void);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector libcrux_ml_kem_vector_neon_ZERO_61(void);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_i16_array(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_i16_array_61(Eurydice_slice array);

Eurydice_arr_e2
libcrux_ml_kem_vector_neon_vector_type_to_i16_array(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_neon_to_i16_array_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_bytes(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_bytes_61(Eurydice_slice array);

void
libcrux_ml_kem_vector_neon_vector_type_to_bytes(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  Eurydice_slice bytes
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
void
libcrux_ml_kem_vector_neon_to_bytes_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x,
  Eurydice_slice bytes
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_add(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_add_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_sub(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_sub_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t c
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_multiply_by_constant_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t c
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_cond_subtract_3329_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

#define LIBCRUX_ML_KEM_VECTOR_NEON_ARITHMETIC_BARRETT_MULTIPLIER ((int16_t)20159)

int16x8_t libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(int16x8_t v);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_barrett_reduce_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
  int16x8_t low,
  int16x8_t high
);

int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
  int16x8_t v,
  int16_t c
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t c
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t c
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t c
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_to_unsigned_representative(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_to_unsigned_representative_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_compress_1(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_1_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

int16_t
libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(int16_t coefficient_bits);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_decompress_1(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_decompress_1_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(int16x8_t v, int16x8_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_1_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta1,
  int16_t zeta2
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_2_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta1,
  int16_t zeta2
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_3_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta1,
  int16_t zeta2
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta1,
  int16_t zeta2
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v,
  int16_t zeta
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a,
  int16_t zeta
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_multiply(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_multiply_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3,
  int16_t zeta4
);

Eurydice_arr_8b
libcrux_ml_kem_vector_neon_serialize_serialize_1(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_8b
libcrux_ml_kem_vector_neon_serialize_1_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_1(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_1_61(Eurydice_slice a);

Eurydice_arr_c4
libcrux_ml_kem_vector_neon_serialize_serialize_4(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_c4
libcrux_ml_kem_vector_neon_serialize_4_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_4(Eurydice_slice v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_4_61(Eurydice_slice a);

Eurydice_arr_77
libcrux_ml_kem_vector_neon_serialize_serialize_5(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_77
libcrux_ml_kem_vector_neon_serialize_5_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_5(Eurydice_slice v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_5_61(Eurydice_slice a);

Eurydice_arr_dc
libcrux_ml_kem_vector_neon_serialize_serialize_10(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_dc
libcrux_ml_kem_vector_neon_serialize_10_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_10(Eurydice_slice v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_10_61(Eurydice_slice a);

Eurydice_arr_f3
libcrux_ml_kem_vector_neon_serialize_serialize_11(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_f3
libcrux_ml_kem_vector_neon_serialize_11_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_11(Eurydice_slice v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_11_61(Eurydice_slice a);

Eurydice_arr_6d
libcrux_ml_kem_vector_neon_serialize_serialize_12(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
Eurydice_arr_6d
libcrux_ml_kem_vector_neon_serialize_12_61(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a
);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_12(Eurydice_slice v);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_12_61(Eurydice_slice a);

size_t libcrux_ml_kem_vector_neon_rej_sample(Eurydice_slice a, Eurydice_slice result);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
size_t libcrux_ml_kem_vector_neon_rej_sample_61(Eurydice_slice a, Eurydice_slice out);

/**
This function found in impl {core::clone::Clone for libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_clone_74(
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *self
);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem_neon_H_DEFINED
#endif /* libcrux_mlkem_neon_H */
