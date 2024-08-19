/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: c3d49544236797e54bfa10f65e4c2b17b543fd30
 * Libcrux: 60b28afb7bf09eeff64f7bd63b12a821496645f2
 */

#ifndef __libcrux_mlkem_neon_H
#define __libcrux_mlkem_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_mlkem_portable.h"
#include "libcrux_sha3_neon.h"

void libcrux_ml_kem_hash_functions_neon_G(Eurydice_slice input,
                                          uint8_t ret[64U]);

void libcrux_ml_kem_hash_functions_neon_H(Eurydice_slice input,
                                          uint8_t ret[32U]);

typedef struct libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector_s {
  core_core_arch_arm_shared_neon_int16x8_t low;
  core_core_arch_arm_shared_neon_int16x8_t high;
} libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector;

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_ZERO(void);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ZERO_20(void);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_from_i16_array(Eurydice_slice array);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_from_i16_array_20(Eurydice_slice array);

void libcrux_ml_kem_vector_neon_vector_type_to_i16_array(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t ret[16U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_to_i16_array_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector x, int16_t ret[16U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_add(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_add_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_sub(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_sub_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_multiply_by_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_bitwise_and_with_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_cond_subtract_3329_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

#define LIBCRUX_ML_KEM_VECTOR_NEON_ARITHMETIC_BARRETT_MULTIPLIER \
  ((int16_t)20159)

core_core_arch_arm_shared_neon_int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce_int16x8_t(
    core_core_arch_arm_shared_neon_int16x8_t v);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_barrett_reduce_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

core_core_arch_arm_shared_neon_int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_reduce_int16x8_t(
    core_core_arch_arm_shared_neon_int16x8_t low,
    core_core_arch_arm_shared_neon_int16x8_t high);

core_core_arch_arm_shared_neon_int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant_int16x8_t(
    core_core_arch_arm_shared_neon_int16x8_t v, int16_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_montgomery_multiply_by_constant_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_compress_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_compress_1_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v);

int16_t libcrux_ml_kem_vector_neon_compress_mask_n_least_significant_bits(
    int16_t coefficient_bits);

core_core_arch_arm_shared_neon_int16x8_t
libcrux_ml_kem_vector_neon_arithmetic_montgomery_multiply_int16x8_t(
    core_core_arch_arm_shared_neon_int16x8_t v,
    core_core_arch_arm_shared_neon_int16x8_t c);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_1_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_2_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_layer_3_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_1_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta1,
    int16_t zeta2);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_2_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta1,
    int16_t zeta2);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, int16_t zeta);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_inv_ntt_layer_3_step_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, int16_t zeta);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_ntt_multiply(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_ntt_multiply_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *lhs,
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *rhs, int16_t zeta1,
    int16_t zeta2, int16_t zeta3, int16_t zeta4);

void libcrux_ml_kem_vector_neon_serialize_serialize_1(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[2U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_1_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[2U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_1(Eurydice_slice a);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_1_20(Eurydice_slice a);

void libcrux_ml_kem_vector_neon_serialize_serialize_4(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[8U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_4_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[8U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_4(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_4_20(Eurydice_slice a);

void libcrux_ml_kem_vector_neon_serialize_serialize_5(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[10U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_5_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[10U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_5(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_5_20(Eurydice_slice a);

void libcrux_ml_kem_vector_neon_serialize_serialize_10(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[20U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_10_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[20U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_10(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_10_20(Eurydice_slice a);

void libcrux_ml_kem_vector_neon_serialize_serialize_11(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[22U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_11_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[22U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_11(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_11_20(Eurydice_slice a);

void libcrux_ml_kem_vector_neon_serialize_serialize_12(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector v, uint8_t ret[24U]);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
void libcrux_ml_kem_vector_neon_serialize_12_20(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector a, uint8_t ret[24U]);

libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_serialize_deserialize_12(Eurydice_slice v);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_deserialize_12_20(Eurydice_slice a);

size_t libcrux_ml_kem_vector_neon_rej_sample(Eurydice_slice a,
                                             Eurydice_slice result);

/**
This function found in impl {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
size_t libcrux_ml_kem_vector_neon_rej_sample_20(Eurydice_slice a,
                                                Eurydice_slice out);

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector)}
*/
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
libcrux_ml_kem_vector_neon_vector_type_clone_ed(
    libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector *self);

/**
A monomorphic instance of libcrux_ml_kem.polynomial.PolynomialRingElement
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector

*/
typedef struct libcrux_ml_kem_polynomial_PolynomialRingElement_1c_s {
  libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector coefficients[16U];
} libcrux_ml_kem_polynomial_PolynomialRingElement_1c;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_66_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_66
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_66;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[2U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[2U][2U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_66 ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_66 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_fd_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_fd
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_fd;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[3U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[3U][3U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_fd_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_fd ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_fd;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_fd private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_fd public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_fd;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c secret_as_ntt[4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_2c_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_2c
      ind_cpa_private_key;
  uint8_t implicit_rejection_value[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_2c;

/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c t_as_ntt[4U];
  uint8_t seed_for_A[32U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1c A[4U][4U];
} libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_2c_s {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_2c ind_cpa_public_key;
  uint8_t public_key_hash[32U];
} libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_2c;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemKeyPairUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c_s {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_2c private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_2c public_key;
} libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_2c;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem_neon_H_DEFINED
#endif
