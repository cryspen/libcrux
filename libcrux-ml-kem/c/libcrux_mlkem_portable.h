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


#ifndef libcrux_mlkem_portable_H
#define libcrux_mlkem_portable_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"

libcrux_sha3_Sha3_512Digest libcrux_ml_kem_hash_functions_portable_G(Eurydice_slice input);

Eurydice_arr_60 libcrux_ml_kem_hash_functions_portable_H(Eurydice_slice input);

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS ((int16_t)1353)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS ((int16_t)3329)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R (62209U)

typedef struct int16_t_x8_s
{
  int16_t fst;
  int16_t snd;
  int16_t thd;
  int16_t f3;
  int16_t f4;
  int16_t f5;
  int16_t f6;
  int16_t f7;
}
int16_t_x8;

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_4(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_4(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_4_b8(Eurydice_slice a);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_vector_type_to_i16_array(Eurydice_arr_e2 x);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_to_i16_array_b8(Eurydice_arr_e2 x);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_from_i16_array_b8(Eurydice_slice array);

typedef struct uint8_t_x5_s
{
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
}
uint8_t_x5;

uint8_t_x5 libcrux_ml_kem_vector_portable_serialize_serialize_5_int(Eurydice_slice v);

Eurydice_arr_77 libcrux_ml_kem_vector_portable_serialize_serialize_5(Eurydice_arr_e2 v);

Eurydice_arr_77 libcrux_ml_kem_vector_portable_serialize_5(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_77 libcrux_ml_kem_vector_portable_serialize_5_b8(Eurydice_arr_e2 a);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_5(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_5(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_5_b8(Eurydice_slice a);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_10(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_10(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_10_b8(Eurydice_slice a);

typedef struct uint8_t_x11_s
{
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
  uint8_t f5;
  uint8_t f6;
  uint8_t f7;
  uint8_t f8;
  uint8_t f9;
  uint8_t f10;
}
uint8_t_x11;

uint8_t_x11 libcrux_ml_kem_vector_portable_serialize_serialize_11_int(Eurydice_slice v);

Eurydice_arr_f3 libcrux_ml_kem_vector_portable_serialize_serialize_11(Eurydice_arr_e2 v);

Eurydice_arr_f3 libcrux_ml_kem_vector_portable_serialize_11(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_f3 libcrux_ml_kem_vector_portable_serialize_11_b8(Eurydice_arr_e2 a);

int16_t_x8 libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_11(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_11(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_11_b8(Eurydice_slice a);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ZERO_b8(void);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_vector_type_from_bytes(Eurydice_slice array);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_from_bytes_b8(Eurydice_slice array);

void
libcrux_ml_kem_vector_portable_vector_type_to_bytes(Eurydice_arr_e2 x, Eurydice_slice bytes);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_to_bytes_b8(Eurydice_arr_e2 x, Eurydice_slice bytes);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_add(Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_add_b8(Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_sub(Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_sub_b8(Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(Eurydice_arr_e2 vec, int16_t c);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_multiply_by_constant_b8(Eurydice_arr_e2 vec, int16_t c);

/**
 Note: This function is not secret independent
 Only use with public values.
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(Eurydice_arr_e2 vec);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(Eurydice_arr_e2 v);

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER ((int32_t)20159)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT ((int32_t)26)

#define LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_R ((int32_t)1 << (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT)

/**
 Signed Barrett Reduction

 Given an input `value`, `barrett_reduce` outputs a representative `result`
 such that:

 - result ≡ value (mod FIELD_MODULUS)
 - the absolute value of `result` is bound as follows:

 `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)

 Note: The input bound is 28296 to prevent overflow in the multiplication of quotient by FIELD_MODULUS

*/
int16_t libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(int16_t value);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(Eurydice_arr_e2 vec);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_barrett_reduce_b8(Eurydice_arr_e2 vector);

#define LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (16U)

/**
 Signed Montgomery Reduction

 Given an input `value`, `montgomery_reduce` outputs a representative `o`
 such that:

 - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
 - the absolute value of `o` is bound as follows:

 `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665

 In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS-1`.
 And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <= FIELD_MODULUS + 1664

*/
int16_t libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(int32_t value);

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
 `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
*/
int16_t
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
  int16_t fe,
  int16_t fer
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
  Eurydice_arr_e2 vec,
  int16_t c
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
  Eurydice_arr_e2 vector,
  int16_t constant
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
  Eurydice_arr_e2 vec,
  int16_t c
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(Eurydice_arr_e2 a);

/**
 The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
 203 standard (Page 18, Expression 4.5), which is defined as:

 ```plaintext
 Compress_d: ℤq -> ℤ_{2ᵈ}
 Compress_d(x) = ⌈(2ᵈ/q)·x⌋
 ```

 Since `⌈x⌋ = ⌊x + 1/2⌋` we have:

 ```plaintext
 Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
               = ⌊(2^{d+1}·x + q) / 2q⌋
 ```

 For further information about the function implementations, consult the
 `implementation_notes.pdf` document in this directory.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
uint8_t libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(uint16_t fe);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_compress_compress_1(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_compress_1_b8(Eurydice_arr_e2 a);

uint32_t
libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
  uint8_t n,
  uint32_t value
);

int16_t
libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
  uint8_t coefficient_bits,
  uint16_t fe
);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_compress_decompress_1(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_decompress_1_b8(Eurydice_arr_e2 a);

void
libcrux_ml_kem_vector_portable_ntt_ntt_step(
  Eurydice_arr_e2 *vec,
  int16_t zeta,
  size_t i,
  size_t j
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(
  Eurydice_arr_e2 vec,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
  Eurydice_arr_e2 a,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(
  Eurydice_arr_e2 vec,
  int16_t zeta0,
  int16_t zeta1
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
  Eurydice_arr_e2 a,
  int16_t zeta0,
  int16_t zeta1
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(Eurydice_arr_e2 vec, int16_t zeta);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(Eurydice_arr_e2 a, int16_t zeta);

void
libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(
  Eurydice_arr_e2 *vec,
  int16_t zeta,
  size_t i,
  size_t j
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
  Eurydice_arr_e2 vec,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
  Eurydice_arr_e2 a,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
  Eurydice_arr_e2 vec,
  int16_t zeta0,
  int16_t zeta1
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
  Eurydice_arr_e2 a,
  int16_t zeta0,
  int16_t zeta1
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(Eurydice_arr_e2 vec, int16_t zeta);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(Eurydice_arr_e2 a, int16_t zeta);

/**
 Compute the product of two Kyber binomials with respect to the
 modulus `X² - zeta`.

 This function almost implements <strong>Algorithm 11</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
 Input: γ ∈ ℤq.
 Output: c₀, c₁ ∈ ℤq.

 c₀ ← a₀·b₀ + a₁·b₁·γ
 c₁ ← a₀·b₁ + a₁·b₀
 return c₀, c₁
 ```
 We say "almost" because the coefficients output by this function are in
 the Montgomery domain (unlike in the specification).

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
void
libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
  Eurydice_arr_e2 *a,
  Eurydice_arr_e2 *b,
  int16_t zeta,
  size_t i,
  Eurydice_arr_e2 *out
);

Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
  Eurydice_arr_e2 *lhs,
  Eurydice_arr_e2 *rhs,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_multiply_b8(
  Eurydice_arr_e2 *lhs,
  Eurydice_arr_e2 *rhs,
  int16_t zeta0,
  int16_t zeta1,
  int16_t zeta2,
  int16_t zeta3
);

Eurydice_arr_8b libcrux_ml_kem_vector_portable_serialize_serialize_1(Eurydice_arr_e2 v);

Eurydice_arr_8b libcrux_ml_kem_vector_portable_serialize_1(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_8b libcrux_ml_kem_vector_portable_serialize_1_b8(Eurydice_arr_e2 a);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_1(Eurydice_slice v);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_1(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_1_b8(Eurydice_slice a);

typedef struct uint8_t_x4_s
{
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
}
uint8_t_x4;

uint8_t_x4 libcrux_ml_kem_vector_portable_serialize_serialize_4_int(Eurydice_slice v);

Eurydice_arr_c4 libcrux_ml_kem_vector_portable_serialize_serialize_4(Eurydice_arr_e2 v);

Eurydice_arr_c4 libcrux_ml_kem_vector_portable_serialize_4(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_c4 libcrux_ml_kem_vector_portable_serialize_4_b8(Eurydice_arr_e2 a);

uint8_t_x5 libcrux_ml_kem_vector_portable_serialize_serialize_10_int(Eurydice_slice v);

Eurydice_arr_dc libcrux_ml_kem_vector_portable_serialize_serialize_10(Eurydice_arr_e2 v);

Eurydice_arr_dc libcrux_ml_kem_vector_portable_serialize_10(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_dc libcrux_ml_kem_vector_portable_serialize_10_b8(Eurydice_arr_e2 a);

typedef struct uint8_t_x3_s
{
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
}
uint8_t_x3;

uint8_t_x3 libcrux_ml_kem_vector_portable_serialize_serialize_12_int(Eurydice_slice v);

Eurydice_arr_6d libcrux_ml_kem_vector_portable_serialize_serialize_12(Eurydice_arr_e2 v);

Eurydice_arr_6d libcrux_ml_kem_vector_portable_serialize_12(Eurydice_arr_e2 a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_6d libcrux_ml_kem_vector_portable_serialize_12_b8(Eurydice_arr_e2 a);

typedef struct int16_t_x2_s
{
  int16_t fst;
  int16_t snd;
}
int16_t_x2;

int16_t_x2 libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_serialize_deserialize_12(Eurydice_slice bytes);

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_12(Eurydice_slice a);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_12_b8(Eurydice_slice a);

size_t
libcrux_ml_kem_vector_portable_sampling_rej_sample(Eurydice_slice a, Eurydice_slice result);

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
size_t libcrux_ml_kem_vector_portable_rej_sample_b8(Eurydice_slice a, Eurydice_slice out);

/**
This function found in impl {core::clone::Clone for libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_vector_type_clone_9c(Eurydice_arr_e2 *self);

#if defined(__cplusplus)
}
#endif

#define libcrux_mlkem_portable_H_DEFINED
#endif /* libcrux_mlkem_portable_H */
