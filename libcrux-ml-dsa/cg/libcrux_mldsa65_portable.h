/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a68994d00017b76a805d0115ca06c1f2c1805e79
 * Eurydice: b665364a6d86749566ce2d650d13fa12c8fab2c5
 * Karamel: 96572bc631fde691a2aea7bce5a5a3838b3a5968
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: 5a0f22fa8387080e4c4e4ac018aaddcdf944e4be
 */

#ifndef __libcrux_mldsa65_portable_H
#define __libcrux_mldsa65_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"
#include "libcrux_sha3_portable.h"

#define LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT ((size_t)8U)

#define LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT \
  (LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT /    \
   LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT)

#define LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T ((size_t)13U)

#define LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH \
  ((size_t)23U)

#define LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T         \
  (LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - \
   LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T)

#define LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN ((size_t)255U)

#define LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS ((int32_t)8380417)

#define LIBCRUX_ML_DSA_CONSTANTS_KEY_GENERATION_RANDOMNESS_SIZE ((size_t)32U)

#define LIBCRUX_ML_DSA_CONSTANTS_MASK_SEED_SIZE ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_MESSAGE_REPRESENTATIVE_SIZE ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN ((size_t)814U)

#define LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE \
  (LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T *     \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE \
  (LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T *     \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE ((size_t)32U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE ((size_t)64U)

#define LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE ((size_t)32U)

#define LIBCRUX_ML_DSA_CONSTANTS_SIGNING_RANDOMNESS_SIZE ((size_t)32U)

#define LIBCRUX_ML_DSA_ENCODING_COMMITMENT_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)6U)

#define LIBCRUX_ML_DSA_ENCODING_ERROR_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)4U)

#define LIBCRUX_ML_DSA_ENCODING_GAMMA1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)20U)

#define LIBCRUX_ML_DSA_ENCODING_T0_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)13U)

#define LIBCRUX_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)10U)

typedef struct libcrux_ml_dsa_hash_functions_portable_Shake128X4_s {
  libcrux_sha3_generic_keccak_KeccakState_17 state0;
  libcrux_sha3_generic_keccak_KeccakState_17 state1;
  libcrux_sha3_generic_keccak_KeccakState_17 state2;
  libcrux_sha3_generic_keccak_KeccakState_17 state3;
} libcrux_ml_dsa_hash_functions_portable_Shake128X4;

static KRML_MUSTINLINE libcrux_ml_dsa_hash_functions_portable_Shake128X4
libcrux_ml_dsa_hash_functions_portable_init_absorb(Eurydice_slice input0,
                                                   Eurydice_slice input1,
                                                   Eurydice_slice input2,
                                                   Eurydice_slice input3) {
  libcrux_sha3_generic_keccak_KeccakState_17 state0 =
      libcrux_sha3_portable_incremental_shake128_init();
  libcrux_sha3_portable_incremental_shake128_absorb_final(&state0, input0);
  libcrux_sha3_generic_keccak_KeccakState_17 state1 =
      libcrux_sha3_portable_incremental_shake128_init();
  libcrux_sha3_portable_incremental_shake128_absorb_final(&state1, input1);
  libcrux_sha3_generic_keccak_KeccakState_17 state2 =
      libcrux_sha3_portable_incremental_shake128_init();
  libcrux_sha3_portable_incremental_shake128_absorb_final(&state2, input2);
  libcrux_sha3_generic_keccak_KeccakState_17 state3 =
      libcrux_sha3_portable_incremental_shake128_init();
  libcrux_sha3_portable_incremental_shake128_absorb_final(&state3, input3);
  return (CLITERAL(libcrux_ml_dsa_hash_functions_portable_Shake128X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

typedef libcrux_sha3_portable_KeccakState
    libcrux_ml_dsa_hash_functions_portable_Shake256;

static KRML_MUSTINLINE libcrux_sha3_portable_KeccakState
libcrux_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_slice input) {
  libcrux_sha3_generic_keccak_KeccakState_17 state =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state, input);
  return state;
}

typedef struct libcrux_ml_dsa_hash_functions_portable_Shake256X4_s {
  libcrux_sha3_generic_keccak_KeccakState_17 state0;
  libcrux_sha3_generic_keccak_KeccakState_17 state1;
  libcrux_sha3_generic_keccak_KeccakState_17 state2;
  libcrux_sha3_generic_keccak_KeccakState_17 state3;
} libcrux_ml_dsa_hash_functions_portable_Shake256X4;

static KRML_MUSTINLINE libcrux_ml_dsa_hash_functions_portable_Shake256X4
libcrux_ml_dsa_hash_functions_portable_init_absorb_x4(Eurydice_slice input0,
                                                      Eurydice_slice input1,
                                                      Eurydice_slice input2,
                                                      Eurydice_slice input3) {
  libcrux_sha3_generic_keccak_KeccakState_17 state0 =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state0, input0);
  libcrux_sha3_generic_keccak_KeccakState_17 state1 =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state1, input1);
  libcrux_sha3_generic_keccak_KeccakState_17 state2 =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state2, input2);
  libcrux_sha3_generic_keccak_KeccakState_17 state3 =
      libcrux_sha3_portable_incremental_shake256_init();
  libcrux_sha3_portable_incremental_shake256_absorb_final(&state3, input3);
  return (CLITERAL(libcrux_ml_dsa_hash_functions_portable_Shake256X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_sha3_portable_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

typedef struct uint8_t_136size_t__x4_s {
  uint8_t fst[136U];
  uint8_t snd[136U];
  uint8_t thd[136U];
  uint8_t f3[136U];
} uint8_t_136size_t__x4;

static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_x4(
    libcrux_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  uint8_t out0[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state0, Eurydice_array_to_slice((size_t)136U, out0, uint8_t));
  uint8_t out1[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state1, Eurydice_array_to_slice((size_t)136U, out1, uint8_t));
  uint8_t out2[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state2, Eurydice_array_to_slice((size_t)136U, out2, uint8_t));
  uint8_t out3[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_first_block(
      &state->state3, Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_first_five_blocks(
    libcrux_ml_dsa_hash_functions_portable_Shake128X4 *state, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state0, Eurydice_array_to_slice((size_t)840U, out0, uint8_t));
  libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state1, Eurydice_array_to_slice((size_t)840U, out1, uint8_t));
  libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state2, Eurydice_array_to_slice((size_t)840U, out2, uint8_t));
  libcrux_sha3_portable_incremental_shake128_squeeze_first_five_blocks(
      &state->state3, Eurydice_array_to_slice((size_t)840U, out3, uint8_t));
}

typedef struct uint8_t_168size_t__x4_s {
  uint8_t fst[168U];
  uint8_t snd[168U];
  uint8_t thd[168U];
  uint8_t f3[168U];
} uint8_t_168size_t__x4;

static KRML_MUSTINLINE uint8_t_168size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block(
    libcrux_ml_dsa_hash_functions_portable_Shake128X4 *state) {
  uint8_t out0[168U] = {0U};
  libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice((size_t)168U, out0, uint8_t));
  uint8_t out1[168U] = {0U};
  libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice((size_t)168U, out1, uint8_t));
  uint8_t out2[168U] = {0U};
  libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice((size_t)168U, out2, uint8_t));
  uint8_t out3[168U] = {0U};
  libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice((size_t)168U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[168U];
  memcpy(copy_of_out0, out0, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[168U];
  memcpy(copy_of_out1, out1, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[168U];
  memcpy(copy_of_out2, out2, (size_t)168U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[168U];
  memcpy(copy_of_out3, out3, (size_t)168U * sizeof(uint8_t));
  uint8_t_168size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)168U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)168U * sizeof(uint8_t));
  return lit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_sha3_portable_KeccakState *state, uint8_t ret[136U]) {
  uint8_t out[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice((size_t)136U, out, uint8_t));
  memcpy(ret, out, (size_t)136U * sizeof(uint8_t));
}

static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4(
    libcrux_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  uint8_t out0[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice((size_t)136U, out0, uint8_t));
  uint8_t out1[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice((size_t)136U, out1, uint8_t));
  uint8_t out2[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice((size_t)136U, out2, uint8_t));
  uint8_t out3[136U] = {0U};
  libcrux_sha3_portable_incremental_shake256_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice((size_t)136U, out3, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out0[136U];
  memcpy(copy_of_out0, out0, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out1[136U];
  memcpy(copy_of_out1, out1, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out2[136U];
  memcpy(copy_of_out2, out2, (size_t)136U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_out3[136U];
  memcpy(copy_of_out3, out3, (size_t)136U * sizeof(uint8_t));
  uint8_t_136size_t__x4 lit;
  memcpy(lit.fst, copy_of_out0, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_out1, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.thd, copy_of_out2, (size_t)136U * sizeof(uint8_t));
  memcpy(lit.f3, copy_of_out3, (size_t)136U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake128X4)}
*/
static KRML_MUSTINLINE libcrux_ml_dsa_hash_functions_portable_Shake128X4
libcrux_ml_dsa_hash_functions_portable_init_absorb_ed(Eurydice_slice input0,
                                                      Eurydice_slice input1,
                                                      Eurydice_slice input2,
                                                      Eurydice_slice input3) {
  return libcrux_ml_dsa_hash_functions_portable_init_absorb(input0, input1,
                                                            input2, input3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake128X4)}
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_ed(
    libcrux_ml_dsa_hash_functions_portable_Shake128X4 *self, uint8_t *out0,
    uint8_t *out1, uint8_t *out2, uint8_t *out3) {
  libcrux_ml_dsa_hash_functions_portable_squeeze_first_five_blocks(
      self, out0, out1, out2, out3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake128::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake128X4)}
*/
static KRML_MUSTINLINE uint8_t_168size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_ed(
    libcrux_ml_dsa_hash_functions_portable_Shake128X4 *self) {
  return libcrux_ml_dsa_hash_functions_portable_squeeze_next_block(self);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::portable::Shake256)#2}
*/
static KRML_MUSTINLINE libcrux_sha3_portable_KeccakState
libcrux_ml_dsa_hash_functions_portable_init_absorb_final_5c(
    Eurydice_slice input) {
  return libcrux_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
      input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::portable::Shake256)#2}
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_5c(
    libcrux_sha3_portable_KeccakState *self, uint8_t ret[136U]) {
  libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(self,
                                                                      ret);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::portable::Shake256)#2}
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_5c(
    libcrux_sha3_portable_KeccakState *self, uint8_t ret[136U]) {
  libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(self, ret);
}

typedef libcrux_sha3_portable_incremental_Shake256Xof
    libcrux_ml_dsa_hash_functions_portable_Shake256Xof;

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::Xof for
libcrux_ml_dsa::hash_functions::portable::Shake256Xof)#4}
*/
static inline void libcrux_ml_dsa_hash_functions_portable_absorb_83(
    libcrux_sha3_portable_incremental_Shake256Xof *self, Eurydice_slice input) {
  libcrux_sha3_portable_incremental_absorb_68(self, input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::Xof for
libcrux_ml_dsa::hash_functions::portable::Shake256Xof)#4}
*/
static inline void libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
    libcrux_sha3_portable_incremental_Shake256Xof *self, Eurydice_slice input) {
  libcrux_sha3_portable_incremental_absorb_final_68(self, input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::Xof for
libcrux_ml_dsa::hash_functions::portable::Shake256Xof)#4}
*/
static inline libcrux_sha3_portable_incremental_Shake256Xof
libcrux_ml_dsa_hash_functions_portable_init_83(void) {
  return libcrux_sha3_portable_incremental_new_68();
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::Xof for
libcrux_ml_dsa::hash_functions::portable::Shake256Xof)#4}
*/
static inline void libcrux_ml_dsa_hash_functions_portable_squeeze_83(
    libcrux_sha3_portable_incremental_Shake256Xof *self, Eurydice_slice out) {
  libcrux_sha3_portable_incremental_squeeze_68(self, out);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake256X4)#3}
*/
static KRML_MUSTINLINE libcrux_ml_dsa_hash_functions_portable_Shake256X4
libcrux_ml_dsa_hash_functions_portable_init_absorb_x4_50(
    Eurydice_slice input0, Eurydice_slice input1, Eurydice_slice input2,
    Eurydice_slice input3) {
  return libcrux_ml_dsa_hash_functions_portable_init_absorb_x4(input0, input1,
                                                               input2, input3);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake256X4)#3}
*/
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_x4_50(
    libcrux_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_x4(self);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::XofX4
for libcrux_ml_dsa::hash_functions::portable::Shake256X4)#3}
*/
static KRML_MUSTINLINE uint8_t_136size_t__x4
libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4_50(
    libcrux_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4(self);
}

#define LIBCRUX_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE ((size_t)168U)

#define LIBCRUX_ML_DSA_HASH_FUNCTIONS_SHAKE128_FIVE_BLOCKS_SIZE \
  (LIBCRUX_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE * (size_t)5U)

#define LIBCRUX_ML_DSA_HASH_FUNCTIONS_SHAKE256_BLOCK_SIZE ((size_t)136U)

#define LIBCRUX_ML_DSA_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE ((size_t)49U)

#define LIBCRUX_ML_DSA_ML_DSA_65_ETA ((size_t)4U)

#define LIBCRUX_ML_DSA_ML_DSA_65_BETA                              \
  ((int32_t)(LIBCRUX_ML_DSA_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE * \
             LIBCRUX_ML_DSA_ML_DSA_65_ETA))

#define LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT ((size_t)4U)

#define LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT ((size_t)4U)

#define LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT ((size_t)20U)

#define LIBCRUX_ML_DSA_ML_DSA_65_COLUMNS_IN_A ((size_t)5U)

#define LIBCRUX_ML_DSA_ML_DSA_65_COMMITMENT_HASH_SIZE ((size_t)48U)

#define LIBCRUX_ML_DSA_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE \
  (LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT * \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A ((size_t)6U)

#define LIBCRUX_ML_DSA_ML_DSA_65_COMMITMENT_VECTOR_SIZE    \
  (LIBCRUX_ML_DSA_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE * \
   LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A)

#define LIBCRUX_ML_DSA_ML_DSA_65_ERROR_RING_ELEMENT_SIZE \
  (LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT * \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_ML_DSA_65_GAMMA1_EXPONENT ((size_t)19U)

#define LIBCRUX_ML_DSA_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE \
  (LIBCRUX_ML_DSA_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT * \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_ML_DSA_ML_DSA_65_GAMMA2 \
  ((LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS - (int32_t)1) / (int32_t)32)

#define LIBCRUX_ML_DSA_ML_DSA_65_MAX_ONES_IN_HINT ((size_t)55U)

typedef libcrux_ml_dsa_types_MLDSASigningKey_22
    libcrux_ml_dsa_ml_dsa_65_MLDSA65SigningKey;

typedef libcrux_ml_dsa_types_MLDSAVerificationKey_ea
    libcrux_ml_dsa_ml_dsa_65_MLDSA65VerificationKey;

#define LIBCRUX_ML_DSA_ML_DSA_65_SIGNATURE_SIZE            \
  (LIBCRUX_ML_DSA_ML_DSA_65_COMMITMENT_HASH_SIZE +         \
   LIBCRUX_ML_DSA_ML_DSA_65_COLUMNS_IN_A *                 \
       LIBCRUX_ML_DSA_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE + \
   LIBCRUX_ML_DSA_ML_DSA_65_MAX_ONES_IN_HINT +             \
   LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A)

#define LIBCRUX_ML_DSA_ML_DSA_65_SIGNING_KEY_SIZE             \
  (LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +                 \
   LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE +           \
   LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH + \
   (LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A +                      \
    LIBCRUX_ML_DSA_ML_DSA_65_COLUMNS_IN_A) *                  \
       LIBCRUX_ML_DSA_ML_DSA_65_ERROR_RING_ELEMENT_SIZE +     \
   LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A *                       \
       LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE)

#define LIBCRUX_ML_DSA_ML_DSA_65_VERIFICATION_KEY_SIZE                \
  (LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +                         \
   LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *            \
       LIBCRUX_ML_DSA_ML_DSA_65_ROWS_IN_A *                           \
       (LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - \
        LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) /           \
       (size_t)8U)

static KRML_MUSTINLINE uint16_t
libcrux_ml_dsa_samplex4_generate_domain_separator(uint8_t row, uint8_t column) {
  return (uint32_t)(uint16_t)column | (uint32_t)(uint16_t)row << 8U;
}

#define LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS ((int32_t)8380417)

#define LIBCRUX_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (58728449ULL)

typedef struct libcrux_ml_dsa_pre_hash_DomainSeparationContext_s {
  Eurydice_slice context;
  Option_3f pre_hash_oid;
} libcrux_ml_dsa_pre_hash_DomainSeparationContext;

#define libcrux_ml_dsa_pre_hash_ContextTooLongError 0

typedef uint8_t libcrux_ml_dsa_pre_hash_DomainSeparationError;

/**
A monomorphic instance of core.result.Result
with types libcrux_ml_dsa_pre_hash_DomainSeparationContext,
libcrux_ml_dsa_pre_hash_DomainSeparationError

*/
typedef struct Result_a8_s {
  Result_a9_tags tag;
  union {
    libcrux_ml_dsa_pre_hash_DomainSeparationContext case_Ok;
    libcrux_ml_dsa_pre_hash_DomainSeparationError case_Err;
  } val;
} Result_a8;

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_ml_dsa::pre_hash::DomainSeparationContext<'a>#1}
*/
static inline Result_a8 libcrux_ml_dsa_pre_hash_new_45(Eurydice_slice context,
                                                       Option_3f pre_hash_oid) {
  Result_a8 uu____0;
  if (Eurydice_slice_len(context, uint8_t) >
      LIBCRUX_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN) {
    uu____0 = (CLITERAL(Result_a8){
        .tag = Err,
        .val = {.case_Err = libcrux_ml_dsa_pre_hash_ContextTooLongError}});
  } else {
    uu____0 = (CLITERAL(Result_a8){
        .tag = Ok,
        .val = {
            .case_Ok = {.context = context, .pre_hash_oid = pre_hash_oid}}});
  }
  return uu____0;
}

typedef struct libcrux_ml_dsa_pre_hash_SHAKE128_PH_s {
} libcrux_ml_dsa_pre_hash_SHAKE128_PH;

typedef struct libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_s {
  int32_t coefficients[8U];
} libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit;

static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_vector_type_ZERO(void) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit lit;
  lit.coefficients[0U] = (int32_t)0;
  lit.coefficients[1U] = (int32_t)0;
  lit.coefficients[2U] = (int32_t)0;
  lit.coefficients[3U] = (int32_t)0;
  lit.coefficients[4U] = (int32_t)0;
  lit.coefficients[5U] = (int32_t)0;
  lit.coefficients[6U] = (int32_t)0;
  lit.coefficients[7U] = (int32_t)0;
  return lit;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_ZERO_36(void) {
  return libcrux_ml_dsa_simd_portable_vector_type_ZERO();
}

static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_slice array) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit lit;
  int32_t ret[8U];
  Result_6c dst;
  Eurydice_slice_to_array2(
      &dst, Eurydice_slice_subslice2(array, (size_t)0U, (size_t)8U, int32_t),
      Eurydice_slice, int32_t[8U]);
  unwrap_26_55(dst, ret);
  memcpy(lit.coefficients, ret, (size_t)8U * sizeof(int32_t));
  return lit;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_from_coefficient_array_36(Eurydice_slice array) {
  return libcrux_ml_dsa_simd_portable_vector_type_from_coefficient_array(array);
}

static inline void
libcrux_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *x,
    int32_t ret[8U]) {
  memcpy(ret, x->coefficients, (size_t)8U * sizeof(int32_t));
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline void libcrux_ml_dsa_simd_portable_to_coefficient_array_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *self,
    int32_t ret[8U]) {
  libcrux_ml_dsa_simd_portable_vector_type_to_coefficient_array(self, ret);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_arithmetic_add(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *rhs) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit sum =
      libcrux_ml_dsa_simd_portable_vector_type_ZERO();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)8U, sum.coefficients, int32_t),
               int32_t);
       i++) {
    size_t i0 = i;
    sum.coefficients[i0] = lhs->coefficients[i0] + rhs->coefficients[i0];
  }
  return sum;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_add_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *rhs) {
  return libcrux_ml_dsa_simd_portable_arithmetic_add(lhs, rhs);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_arithmetic_subtract(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *rhs) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit difference =
      libcrux_ml_dsa_simd_portable_vector_type_ZERO();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)8U, difference.coefficients, int32_t),
                              int32_t);
       i++) {
    size_t i0 = i;
    difference.coefficients[i0] = lhs->coefficients[i0] - rhs->coefficients[i0];
  }
  return difference;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_subtract_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *rhs) {
  return libcrux_ml_dsa_simd_portable_arithmetic_subtract(lhs, rhs);
}

static KRML_MUSTINLINE bool
libcrux_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t bound) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "Eurydice error: Failure(\"TODO: TraitTypes "
                    "core::array::iter::{core::iter::traits::iterator::"
                    "Iterator for core::array::iter::IntoIter<T, "
                    "N>[TraitClause@0]}#2<T@0, C@0>[TraitClause@0]::Item\")\n");
  KRML_HOST_EXIT(255U);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline bool libcrux_ml_dsa_simd_portable_infinity_norm_exceeds_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t bound) {
  return libcrux_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
      simd_unit, bound);
}

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (32U)

static KRML_MUSTINLINE uint64_t
libcrux_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value) {
  return value & ((1ULL << (uint32_t)n) - 1ULL);
}

static KRML_MUSTINLINE int32_t
libcrux_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value) {
  uint64_t t =
      libcrux_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT,
          (uint64_t)value) *
      LIBCRUX_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
  int32_t k = (int32_t)
      libcrux_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT, t);
  int64_t k_times_modulus =
      (int64_t)k * (int64_t)LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
  int32_t c =
      (int32_t)(k_times_modulus >>
                (uint32_t)
                    LIBCRUX_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int32_t value_high =
      (int32_t)(value >>
                (uint32_t)
                    LIBCRUX_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *rhs) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit product =
      libcrux_ml_dsa_simd_portable_vector_type_ZERO();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)8U, product.coefficients, int32_t),
                              int32_t);
       i++) {
    size_t i0 = i;
    product.coefficients[i0] =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)lhs->coefficients[i0] * (int64_t)rhs->coefficients[i0]);
  }
  return product;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_montgomery_multiply_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit lhs,
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit rhs) {
  return libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply(&lhs,
                                                                     &rhs);
}

static KRML_MUSTINLINE int32_t
libcrux_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe) {
  int32_t quotient = (fe + ((int32_t)1 << 22U)) >> 23U;
  return fe - quotient * LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
}

typedef struct libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x2_s {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit fst;
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit snd;
} libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x2;

static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x2
libcrux_ml_dsa_simd_portable_arithmetic_power2round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::array::iter::{core::iter::traits::iterator::Iterator for "
      "core::array::iter::IntoIter<T, N>[TraitClause@0]}#2<i32, 8: "
      "usize>[core::marker::Sized<i32>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x2
libcrux_ml_dsa_simd_portable_power2round_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit) {
  return libcrux_ml_dsa_simd_portable_arithmetic_power2round(simd_unit);
}

static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          core_slice___Slice_T___chunks(randomness, (size_t)3U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, core_slice_iter_Chunks);
  while (true) {
    Option_1b uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T__TraitClause_0___71__next(
            &iter, uint8_t, Option_1b);
    if (uu____0.tag == None) {
      break;
    } else {
      Eurydice_slice bytes = uu____0.f0;
      int32_t b0 =
          (int32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *);
      int32_t b1 =
          (int32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *);
      int32_t b2 =
          (int32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *);
      int32_t coefficient = ((b2 << 16U | b1 << 8U) | b0) & (int32_t)8388607;
      if (coefficient < LIBCRUX_ML_DSA_CONSTANTS_FIELD_MODULUS) {
        Eurydice_slice_index(out, sampled, int32_t, int32_t *) = coefficient;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline size_t
libcrux_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_36(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
      randomness, out);
}

static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  core_slice_iter_Iter iter =
      core_slice_iter___core__iter__traits__collect__IntoIterator_for___a___Slice_T____1__into_iter(
          randomness, uint8_t, core_slice_iter_Iter);
  while (true) {
    Option_3f uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Iter__a__T__TraitClause_0___182__next(
            &iter, uint8_t, Option_3f);
    if (uu____0.tag == None) {
      break;
    } else {
      uint8_t *byte = uu____0.f0;
      uint8_t try_0 = Eurydice_bitand_pv_u8(byte, 15U);
      uint8_t try_1 = Eurydice_shr_pv_u8(byte, (int32_t)4);
      if (try_0 < 15U) {
        int32_t try_00 = (int32_t)try_0;
        int32_t try_0_mod_5 =
            try_00 - (try_00 * (int32_t)26 >> 7U) * (int32_t)5;
        Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
            (int32_t)2 - try_0_mod_5;
        sampled++;
      }
      if (try_1 < 15U) {
        int32_t try_10 = (int32_t)try_1;
        int32_t try_1_mod_5 =
            try_10 - (try_10 * (int32_t)26 >> 7U) * (int32_t)5;
        Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
            (int32_t)2 - try_1_mod_5;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline size_t
libcrux_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_36(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
      randomness, out);
}

static KRML_MUSTINLINE size_t
libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_slice randomness, Eurydice_slice out) {
  size_t sampled = (size_t)0U;
  core_slice_iter_Iter iter =
      core_slice_iter___core__iter__traits__collect__IntoIterator_for___a___Slice_T____1__into_iter(
          randomness, uint8_t, core_slice_iter_Iter);
  while (true) {
    Option_3f uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Iter__a__T__TraitClause_0___182__next(
            &iter, uint8_t, Option_3f);
    if (uu____0.tag == None) {
      break;
    } else {
      uint8_t *byte = uu____0.f0;
      uint8_t try_0 = Eurydice_bitand_pv_u8(byte, 15U);
      uint8_t try_1 = Eurydice_shr_pv_u8(byte, (int32_t)4);
      if (try_0 < 9U) {
        Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
            (int32_t)4 - (int32_t)try_0;
        sampled++;
      }
      if (try_1 < 9U) {
        Eurydice_slice_index(out, sampled, int32_t, int32_t *) =
            (int32_t)4 - (int32_t)try_1;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline size_t
libcrux_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_36(
    Eurydice_slice randomness, Eurydice_slice out) {
  return libcrux_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
      randomness, out);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_slice serialized) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::ChunksExact<\'a, T>[TraitClause@0]}#90<\'_, "
      "u8>[core::marker::Sized<u8>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_slice serialized) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::ChunksExact<\'a, T>[TraitClause@0]}#90<\'_, "
      "u8>[core::marker::Sized<u8>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA \
  ((int32_t)2)

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_slice serialized) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit =
      libcrux_ml_dsa_simd_portable_vector_type_ZERO();
  int32_t byte0 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *);
  int32_t byte1 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *);
  int32_t byte2 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *);
  simd_unit.coefficients[0U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 & (int32_t)7);
  simd_unit.coefficients[1U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte0 >> 3U & (int32_t)7);
  simd_unit.coefficients[2U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte0 >> 6U | byte1 << 2U) & (int32_t)7);
  simd_unit.coefficients[3U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 1U & (int32_t)7);
  simd_unit.coefficients[4U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte1 >> 4U & (int32_t)7);
  simd_unit.coefficients[5U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      ((byte1 >> 7U | byte2 << 1U) & (int32_t)7);
  simd_unit.coefficients[6U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 2U & (int32_t)7);
  simd_unit.coefficients[7U] =
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA -
      (byte2 >> 5U & (int32_t)7);
  return simd_unit;
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_slice serialized) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "u8>[core::marker::Sized<u8>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

static KRML_MUSTINLINE int32_t
libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(int32_t t0) {
  return ((int32_t)1
          << (uint32_t)(LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                        (size_t)1U)) -
         t0;
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_encoding_t0_serialize(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    uint8_t ret[13U]) {
  uint8_t serialized[13U] = {0U};
  int32_t coefficient0 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[0U]);
  int32_t coefficient1 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[1U]);
  int32_t coefficient2 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[2U]);
  int32_t coefficient3 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[3U]);
  int32_t coefficient4 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[4U]);
  int32_t coefficient5 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[5U]);
  int32_t coefficient6 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[6U]);
  int32_t coefficient7 =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit.coefficients[7U]);
  serialized[0U] = (uint8_t)coefficient0;
  serialized[1U] = (uint8_t)(coefficient0 >> 8U);
  size_t uu____0 = (size_t)1U;
  serialized[uu____0] =
      (uint32_t)serialized[uu____0] | (uint32_t)(uint8_t)(coefficient1 << 5U);
  serialized[2U] = (uint8_t)(coefficient1 >> 3U);
  serialized[3U] = (uint8_t)(coefficient1 >> 11U);
  size_t uu____1 = (size_t)3U;
  serialized[uu____1] =
      (uint32_t)serialized[uu____1] | (uint32_t)(uint8_t)(coefficient2 << 2U);
  serialized[4U] = (uint8_t)(coefficient2 >> 6U);
  size_t uu____2 = (size_t)4U;
  serialized[uu____2] =
      (uint32_t)serialized[uu____2] | (uint32_t)(uint8_t)(coefficient3 << 7U);
  serialized[5U] = (uint8_t)(coefficient3 >> 1U);
  serialized[6U] = (uint8_t)(coefficient3 >> 9U);
  size_t uu____3 = (size_t)6U;
  serialized[uu____3] =
      (uint32_t)serialized[uu____3] | (uint32_t)(uint8_t)(coefficient4 << 4U);
  serialized[7U] = (uint8_t)(coefficient4 >> 4U);
  serialized[8U] = (uint8_t)(coefficient4 >> 12U);
  size_t uu____4 = (size_t)8U;
  serialized[uu____4] =
      (uint32_t)serialized[uu____4] | (uint32_t)(uint8_t)(coefficient5 << 1U);
  serialized[9U] = (uint8_t)(coefficient5 >> 7U);
  size_t uu____5 = (size_t)9U;
  serialized[uu____5] =
      (uint32_t)serialized[uu____5] | (uint32_t)(uint8_t)(coefficient6 << 6U);
  serialized[10U] = (uint8_t)(coefficient6 >> 2U);
  serialized[11U] = (uint8_t)(coefficient6 >> 10U);
  size_t uu____6 = (size_t)11U;
  serialized[uu____6] =
      (uint32_t)serialized[uu____6] | (uint32_t)(uint8_t)(coefficient7 << 3U);
  serialized[12U] = (uint8_t)(coefficient7 >> 5U);
  memcpy(ret, serialized, (size_t)13U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline void libcrux_ml_dsa_simd_portable_t0_serialize_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    uint8_t ret[13U]) {
  libcrux_ml_dsa_simd_portable_encoding_t0_serialize(simd_unit, ret);
}

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK \
  (((int32_t)1 << (uint32_t)(int32_t)                                                     \
        LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) -                               \
   (int32_t)1)

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_slice serialized) {
  int32_t byte0 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)0U, uint8_t, uint8_t *);
  int32_t byte1 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)1U, uint8_t, uint8_t *);
  int32_t byte2 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)2U, uint8_t, uint8_t *);
  int32_t byte3 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)3U, uint8_t, uint8_t *);
  int32_t byte4 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)4U, uint8_t, uint8_t *);
  int32_t byte5 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)5U, uint8_t, uint8_t *);
  int32_t byte6 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)6U, uint8_t, uint8_t *);
  int32_t byte7 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)7U, uint8_t, uint8_t *);
  int32_t byte8 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)8U, uint8_t, uint8_t *);
  int32_t byte9 =
      (int32_t)Eurydice_slice_index(serialized, (size_t)9U, uint8_t, uint8_t *);
  int32_t byte10 = (int32_t)Eurydice_slice_index(serialized, (size_t)10U,
                                                 uint8_t, uint8_t *);
  int32_t byte11 = (int32_t)Eurydice_slice_index(serialized, (size_t)11U,
                                                 uint8_t, uint8_t *);
  int32_t byte12 = (int32_t)Eurydice_slice_index(serialized, (size_t)12U,
                                                 uint8_t, uint8_t *);
  int32_t coefficient0 = byte0;
  coefficient0 = coefficient0 | byte1 << 8U;
  coefficient0 =
      coefficient0 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient1 = byte1 >> 5U;
  coefficient1 = coefficient1 | byte2 << 3U;
  coefficient1 = coefficient1 | byte3 << 11U;
  coefficient1 =
      coefficient1 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient2 = byte3 >> 2U;
  coefficient2 = coefficient2 | byte4 << 6U;
  coefficient2 =
      coefficient2 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient3 = byte4 >> 7U;
  coefficient3 = coefficient3 | byte5 << 1U;
  coefficient3 = coefficient3 | byte6 << 9U;
  coefficient3 =
      coefficient3 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient4 = byte6 >> 4U;
  coefficient4 = coefficient4 | byte7 << 4U;
  coefficient4 = coefficient4 | byte8 << 12U;
  coefficient4 =
      coefficient4 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient5 = byte8 >> 1U;
  coefficient5 = coefficient5 | byte9 << 7U;
  coefficient5 =
      coefficient5 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient6 = byte9 >> 6U;
  coefficient6 = coefficient6 | byte10 << 2U;
  coefficient6 = coefficient6 | byte11 << 10U;
  coefficient6 =
      coefficient6 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient7 = byte11 >> 3U;
  coefficient7 = coefficient7 | byte12 << 5U;
  coefficient7 =
      coefficient7 &
      LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit =
      libcrux_ml_dsa_simd_portable_vector_type_ZERO();
  simd_unit.coefficients[0U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient0);
  simd_unit.coefficients[1U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient1);
  simd_unit.coefficients[2U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient2);
  simd_unit.coefficients[3U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient3);
  simd_unit.coefficients[4U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient4);
  simd_unit.coefficients[5U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient5);
  simd_unit.coefficients[6U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient6);
  simd_unit.coefficients[7U] =
      libcrux_ml_dsa_simd_portable_encoding_t0_change_t0_interval(coefficient7);
  return simd_unit;
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_t0_deserialize_36(Eurydice_slice serialized) {
  return libcrux_ml_dsa_simd_portable_encoding_t0_deserialize(serialized);
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_encoding_t1_serialize(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    uint8_t ret[10U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::ChunksExact<\'a, T>[TraitClause@0]}#90<\'_, "
      "i32>[core::marker::Sized<i32>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline void libcrux_ml_dsa_simd_portable_t1_serialize_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    uint8_t ret[10U]) {
  libcrux_ml_dsa_simd_portable_encoding_t1_serialize(simd_unit, ret);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_slice serialized) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::ChunksExact<\'a, T>[TraitClause@0]}#90<\'_, "
      "u8>[core::marker::Sized<u8>] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_t1_deserialize_36(Eurydice_slice serialized) {
  return libcrux_ml_dsa_simd_portable_encoding_t1_deserialize(serialized);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t c) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(Eurydice_array_to_slice(
                                  (size_t)8U, simd_unit.coefficients, int32_t),
                              int32_t);
       i++) {
    size_t i0 = i;
    simd_unit.coefficients[i0] =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            (int64_t)simd_unit.coefficients[i0] * (int64_t)c);
  }
  return simd_unit;
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_99(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)16U], (int32_t)25847);
    re[j + (size_t)16U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_7(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_99(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_990(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)8U], (int32_t)-2608894);
    re[j + (size_t)8U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)8U], (int32_t)-518909);
    re[j + (size_t)8U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_6(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_990(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_991(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)4U], (int32_t)237124);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a8(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)4U], (int32_t)-777960);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)4U], (int32_t)-876248);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d9(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)4U], (int32_t)466468);
    re[j + (size_t)4U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_5(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_991(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a8(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a0(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d9(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_992(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)1826347);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_6b(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)2353451);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a80(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)-359251);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_95(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)-2091905);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)3119733);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_de(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)-2884855);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d90(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)3111497);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)2U], (int32_t)2680103);
    re[j + (size_t)2U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_4(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_992(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_6b(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a80(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_95(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a1(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_de(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d90(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_993(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)2725464);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_1c(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)1024112);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-1079900);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_44(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)3585928);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a81(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-549488);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_1f(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-1119584);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_950(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)2619752);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-2108549);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-2118186);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_e4(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-3859737);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_de0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-1399561);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_05(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-3277672);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d91(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)1757237);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3a(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)-19422);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)4010497);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit t =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[j + (size_t)1U], (int32_t)280005);
    re[j + (size_t)1U] =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j], &t);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j], &t);
    re[j] = uu____1;
  }
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_3(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_993(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_1c(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_6b0(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_44(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a81(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_1f(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_950(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b0(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_7a2(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_e4(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_de0(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_05(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_d91(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3a(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_3b1(re);
  libcrux_ml_dsa_simd_portable_ntt_outer_3_plus_a0(re);
}

static KRML_MUSTINLINE int32_t
libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer) {
  return libcrux_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
      (int64_t)fe * (int64_t)fer);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta) {
  int32_t t =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[4U], zeta);
  simd_unit.coefficients[4U] = simd_unit.coefficients[0U] - t;
  simd_unit.coefficients[0U] = simd_unit.coefficients[0U] + t;
  int32_t t0 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[5U], zeta);
  simd_unit.coefficients[5U] = simd_unit.coefficients[1U] - t0;
  simd_unit.coefficients[1U] = simd_unit.coefficients[1U] + t0;
  int32_t t1 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[6U], zeta);
  simd_unit.coefficients[6U] = simd_unit.coefficients[2U] - t1;
  simd_unit.coefficients[2U] = simd_unit.coefficients[2U] + t1;
  int32_t t2 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[7U], zeta);
  simd_unit.coefficients[7U] = simd_unit.coefficients[3U] - t2;
  simd_unit.coefficients[3U] = simd_unit.coefficients[3U] + t2;
  return simd_unit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(re[index],
                                                                zeta);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)0U,
                                                        (int32_t)2706023);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)1U,
                                                        (int32_t)95776);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)2U,
                                                        (int32_t)3077325);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)3U,
                                                        (int32_t)3530437);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)4U,
                                                        (int32_t)-1661693);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)5U,
                                                        (int32_t)-3592148);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)6U,
                                                        (int32_t)-2537516);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)7U,
                                                        (int32_t)3915439);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)8U,
                                                        (int32_t)-3861115);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)9U,
                                                        (int32_t)-3043716);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)10U,
                                                        (int32_t)3574422);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)11U,
                                                        (int32_t)-2867647);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)12U,
                                                        (int32_t)3539968);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)13U,
                                                        (int32_t)-300467);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)14U,
                                                        (int32_t)2348700);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)15U,
                                                        (int32_t)-539299);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)16U,
                                                        (int32_t)-1699267);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)17U,
                                                        (int32_t)-1643818);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)18U,
                                                        (int32_t)3505694);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)19U,
                                                        (int32_t)-3821735);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)20U,
                                                        (int32_t)3507263);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)21U,
                                                        (int32_t)-2140649);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)22U,
                                                        (int32_t)-1600420);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)23U,
                                                        (int32_t)3699596);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)24U,
                                                        (int32_t)811944);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)25U,
                                                        (int32_t)531354);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)26U,
                                                        (int32_t)954230);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)27U,
                                                        (int32_t)3881043);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)28U,
                                                        (int32_t)3900724);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)29U,
                                                        (int32_t)-2556880);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)30U,
                                                        (int32_t)2071892);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)31U,
                                                        (int32_t)-2797779);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta1, int32_t zeta2) {
  int32_t t =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[2U], zeta1);
  simd_unit.coefficients[2U] = simd_unit.coefficients[0U] - t;
  simd_unit.coefficients[0U] = simd_unit.coefficients[0U] + t;
  int32_t t0 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[3U], zeta1);
  simd_unit.coefficients[3U] = simd_unit.coefficients[1U] - t0;
  simd_unit.coefficients[1U] = simd_unit.coefficients[1U] + t0;
  int32_t t1 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[6U], zeta2);
  simd_unit.coefficients[6U] = simd_unit.coefficients[4U] - t1;
  simd_unit.coefficients[4U] = simd_unit.coefficients[4U] + t1;
  int32_t t2 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[7U], zeta2);
  simd_unit.coefficients[7U] = simd_unit.coefficients[5U] - t2;
  simd_unit.coefficients[5U] = simd_unit.coefficients[5U] + t2;
  return simd_unit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta_0, int32_t zeta_1) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(re[index],
                                                                zeta_0, zeta_1);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)0U, (int32_t)-3930395, (int32_t)-1528703);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)1U, (int32_t)-3677745, (int32_t)-3041255);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)2U, (int32_t)-1452451, (int32_t)3475950);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)3U, (int32_t)2176455, (int32_t)-1585221);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)4U, (int32_t)-1257611, (int32_t)1939314);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)5U, (int32_t)-4083598, (int32_t)-1000202);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)6U, (int32_t)-3190144, (int32_t)-3157330);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)7U, (int32_t)-3632928, (int32_t)126922);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)8U, (int32_t)3412210, (int32_t)-983419);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)9U, (int32_t)2147896, (int32_t)2715295);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)10U, (int32_t)-2967645, (int32_t)-3693493);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)11U, (int32_t)-411027, (int32_t)-2477047);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)12U, (int32_t)-671102, (int32_t)-1228525);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)13U, (int32_t)-22981, (int32_t)-1308169);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)14U, (int32_t)-381987, (int32_t)1349076);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)15U, (int32_t)1852771, (int32_t)-1430430);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)16U, (int32_t)-3343383, (int32_t)264944);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)17U, (int32_t)508951, (int32_t)3097992);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)18U, (int32_t)44288, (int32_t)-1100098);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)19U, (int32_t)904516, (int32_t)3958618);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)20U, (int32_t)-3724342, (int32_t)-8578);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)21U, (int32_t)1653064, (int32_t)-3249728);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)22U, (int32_t)2389356, (int32_t)-210977);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)23U, (int32_t)759969, (int32_t)-1316856);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)24U, (int32_t)189548, (int32_t)-3553272);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)25U, (int32_t)3159746, (int32_t)-1851402);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)26U, (int32_t)-2409325, (int32_t)-177440);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)27U, (int32_t)1315589, (int32_t)1341330);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)28U, (int32_t)1285669, (int32_t)-1584928);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)29U, (int32_t)-812732, (int32_t)-1439742);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)30U, (int32_t)-3019102, (int32_t)-3881060);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
      re, (size_t)31U, (int32_t)-3628969, (int32_t)3839961);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  int32_t t =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[1U], zeta0);
  simd_unit.coefficients[1U] = simd_unit.coefficients[0U] - t;
  simd_unit.coefficients[0U] = simd_unit.coefficients[0U] + t;
  int32_t t0 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[3U], zeta1);
  simd_unit.coefficients[3U] = simd_unit.coefficients[2U] - t0;
  simd_unit.coefficients[2U] = simd_unit.coefficients[2U] + t0;
  int32_t t1 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[5U], zeta2);
  simd_unit.coefficients[5U] = simd_unit.coefficients[4U] - t1;
  simd_unit.coefficients[4U] = simd_unit.coefficients[4U] + t1;
  int32_t t2 =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit.coefficients[7U], zeta3);
  simd_unit.coefficients[7U] = simd_unit.coefficients[6U] - t2;
  simd_unit.coefficients[6U] = simd_unit.coefficients[6U] + t2;
  return simd_unit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta_0, int32_t zeta_1, int32_t zeta_2, int32_t zeta_3) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
          re[index], zeta_0, zeta_1, zeta_2, zeta_3);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)0U, (int32_t)2091667, (int32_t)3407706, (int32_t)2316500,
      (int32_t)3817976);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)1U, (int32_t)-3342478, (int32_t)2244091, (int32_t)-2446433,
      (int32_t)-3562462);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)2U, (int32_t)266997, (int32_t)2434439, (int32_t)-1235728,
      (int32_t)3513181);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)3U, (int32_t)-3520352, (int32_t)-3759364, (int32_t)-1197226,
      (int32_t)-3193378);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)4U, (int32_t)900702, (int32_t)1859098, (int32_t)909542,
      (int32_t)819034);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)5U, (int32_t)495491, (int32_t)-1613174, (int32_t)-43260,
      (int32_t)-522500);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)6U, (int32_t)-655327, (int32_t)-3122442, (int32_t)2031748,
      (int32_t)3207046);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)7U, (int32_t)-3556995, (int32_t)-525098, (int32_t)-768622,
      (int32_t)-3595838);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)8U, (int32_t)342297, (int32_t)286988, (int32_t)-2437823,
      (int32_t)4108315);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)9U, (int32_t)3437287, (int32_t)-3342277, (int32_t)1735879,
      (int32_t)203044);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)10U, (int32_t)2842341, (int32_t)2691481, (int32_t)-2590150,
      (int32_t)1265009);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)11U, (int32_t)4055324, (int32_t)1247620, (int32_t)2486353,
      (int32_t)1595974);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)12U, (int32_t)-3767016, (int32_t)1250494, (int32_t)2635921,
      (int32_t)-3548272);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)13U, (int32_t)-2994039, (int32_t)1869119, (int32_t)1903435,
      (int32_t)-1050970);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)14U, (int32_t)-1333058, (int32_t)1237275, (int32_t)-3318210,
      (int32_t)-1430225);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)15U, (int32_t)-451100, (int32_t)1312455, (int32_t)3306115,
      (int32_t)-1962642);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)16U, (int32_t)-1279661, (int32_t)1917081, (int32_t)-2546312,
      (int32_t)-1374803);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)17U, (int32_t)1500165, (int32_t)777191, (int32_t)2235880,
      (int32_t)3406031);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)18U, (int32_t)-542412, (int32_t)-2831860, (int32_t)-1671176,
      (int32_t)-1846953);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)19U, (int32_t)-2584293, (int32_t)-3724270, (int32_t)594136,
      (int32_t)-3776993);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)20U, (int32_t)-2013608, (int32_t)2432395, (int32_t)2454455,
      (int32_t)-164721);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)21U, (int32_t)1957272, (int32_t)3369112, (int32_t)185531,
      (int32_t)-1207385);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)22U, (int32_t)-3183426, (int32_t)162844, (int32_t)1616392,
      (int32_t)3014001);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)23U, (int32_t)810149, (int32_t)1652634, (int32_t)-3694233,
      (int32_t)-1799107);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)24U, (int32_t)-3038916, (int32_t)3523897, (int32_t)3866901,
      (int32_t)269760);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)25U, (int32_t)2213111, (int32_t)-975884, (int32_t)1717735,
      (int32_t)472078);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)26U, (int32_t)-426683, (int32_t)1723600, (int32_t)-1803090,
      (int32_t)1910376);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)27U, (int32_t)-1667432, (int32_t)-1104333, (int32_t)-260646,
      (int32_t)-3833893);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)28U, (int32_t)-2939036, (int32_t)-2235985, (int32_t)-420899,
      (int32_t)-2286327);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)29U, (int32_t)183443, (int32_t)-976891, (int32_t)1612842,
      (int32_t)-3545687);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)30U, (int32_t)-554416, (int32_t)3919660, (int32_t)-48306,
      (int32_t)-1362209);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)31U, (int32_t)3937738, (int32_t)1400424, (int32_t)-846154,
      (int32_t)1976782);
}

static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_ntt_ntt(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit re[32U],
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret[32U]) {
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_7(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_6(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_5(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_4(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_3(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_2(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_1(re);
  libcrux_ml_dsa_simd_portable_ntt_ntt_at_layer_0(re);
  memcpy(ret, re,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline void libcrux_ml_dsa_simd_portable_ntt_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_units[32U],
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret[32U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
      copy_of_simd_units[32U];
  memcpy(copy_of_simd_units, simd_units,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret0[32U];
  libcrux_ml_dsa_simd_portable_ntt_ntt(copy_of_simd_units, ret0);
  memcpy(ret, ret0,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  int32_t a_minus_b = simd_unit.coefficients[1U] - simd_unit.coefficients[0U];
  simd_unit.coefficients[0U] =
      simd_unit.coefficients[0U] + simd_unit.coefficients[1U];
  simd_unit.coefficients[1U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit.coefficients[3U] - simd_unit.coefficients[2U];
  simd_unit.coefficients[2U] =
      simd_unit.coefficients[2U] + simd_unit.coefficients[3U];
  simd_unit.coefficients[3U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta1);
  int32_t a_minus_b1 = simd_unit.coefficients[5U] - simd_unit.coefficients[4U];
  simd_unit.coefficients[4U] =
      simd_unit.coefficients[4U] + simd_unit.coefficients[5U];
  simd_unit.coefficients[5U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta2);
  int32_t a_minus_b2 = simd_unit.coefficients[7U] - simd_unit.coefficients[6U];
  simd_unit.coefficients[6U] =
      simd_unit.coefficients[6U] + simd_unit.coefficients[7U];
  simd_unit.coefficients[7U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta3);
  return simd_unit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta0, int32_t zeta1, int32_t zeta2, int32_t zeta3) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
          re[index], zeta0, zeta1, zeta2, zeta3);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)0U, (int32_t)1976782, (int32_t)-846154, (int32_t)1400424,
      (int32_t)3937738);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)1U, (int32_t)-1362209, (int32_t)-48306, (int32_t)3919660,
      (int32_t)-554416);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)2U, (int32_t)-3545687, (int32_t)1612842, (int32_t)-976891,
      (int32_t)183443);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)3U, (int32_t)-2286327, (int32_t)-420899, (int32_t)-2235985,
      (int32_t)-2939036);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)4U, (int32_t)-3833893, (int32_t)-260646, (int32_t)-1104333,
      (int32_t)-1667432);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)5U, (int32_t)1910376, (int32_t)-1803090, (int32_t)1723600,
      (int32_t)-426683);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)6U, (int32_t)472078, (int32_t)1717735, (int32_t)-975884,
      (int32_t)2213111);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)7U, (int32_t)269760, (int32_t)3866901, (int32_t)3523897,
      (int32_t)-3038916);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)8U, (int32_t)-1799107, (int32_t)-3694233, (int32_t)1652634,
      (int32_t)810149);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)9U, (int32_t)3014001, (int32_t)1616392, (int32_t)162844,
      (int32_t)-3183426);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)10U, (int32_t)-1207385, (int32_t)185531, (int32_t)3369112,
      (int32_t)1957272);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)11U, (int32_t)-164721, (int32_t)2454455, (int32_t)2432395,
      (int32_t)-2013608);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)12U, (int32_t)-3776993, (int32_t)594136, (int32_t)-3724270,
      (int32_t)-2584293);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)13U, (int32_t)-1846953, (int32_t)-1671176, (int32_t)-2831860,
      (int32_t)-542412);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)14U, (int32_t)3406031, (int32_t)2235880, (int32_t)777191,
      (int32_t)1500165);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)15U, (int32_t)-1374803, (int32_t)-2546312, (int32_t)1917081,
      (int32_t)-1279661);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)16U, (int32_t)-1962642, (int32_t)3306115, (int32_t)1312455,
      (int32_t)-451100);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)17U, (int32_t)-1430225, (int32_t)-3318210, (int32_t)1237275,
      (int32_t)-1333058);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)18U, (int32_t)-1050970, (int32_t)1903435, (int32_t)1869119,
      (int32_t)-2994039);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)19U, (int32_t)-3548272, (int32_t)2635921, (int32_t)1250494,
      (int32_t)-3767016);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)20U, (int32_t)1595974, (int32_t)2486353, (int32_t)1247620,
      (int32_t)4055324);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)21U, (int32_t)1265009, (int32_t)-2590150, (int32_t)2691481,
      (int32_t)2842341);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)22U, (int32_t)203044, (int32_t)1735879, (int32_t)-3342277,
      (int32_t)3437287);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)23U, (int32_t)4108315, (int32_t)-2437823, (int32_t)286988,
      (int32_t)342297);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)24U, (int32_t)-3595838, (int32_t)-768622, (int32_t)-525098,
      (int32_t)-3556995);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)25U, (int32_t)3207046, (int32_t)2031748, (int32_t)-3122442,
      (int32_t)-655327);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)26U, (int32_t)-522500, (int32_t)-43260, (int32_t)-1613174,
      (int32_t)495491);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)27U, (int32_t)819034, (int32_t)909542, (int32_t)1859098,
      (int32_t)900702);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)28U, (int32_t)-3193378, (int32_t)-1197226, (int32_t)-3759364,
      (int32_t)-3520352);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)29U, (int32_t)3513181, (int32_t)-1235728, (int32_t)2434439,
      (int32_t)266997);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)30U, (int32_t)-3562462, (int32_t)-2446433, (int32_t)2244091,
      (int32_t)-3342478);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)31U, (int32_t)3817976, (int32_t)2316500, (int32_t)3407706,
      (int32_t)2091667);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta0, int32_t zeta1) {
  int32_t a_minus_b = simd_unit.coefficients[2U] - simd_unit.coefficients[0U];
  simd_unit.coefficients[0U] =
      simd_unit.coefficients[0U] + simd_unit.coefficients[2U];
  simd_unit.coefficients[2U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta0);
  int32_t a_minus_b0 = simd_unit.coefficients[3U] - simd_unit.coefficients[1U];
  simd_unit.coefficients[1U] =
      simd_unit.coefficients[1U] + simd_unit.coefficients[3U];
  simd_unit.coefficients[3U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta0);
  int32_t a_minus_b1 = simd_unit.coefficients[6U] - simd_unit.coefficients[4U];
  simd_unit.coefficients[4U] =
      simd_unit.coefficients[4U] + simd_unit.coefficients[6U];
  simd_unit.coefficients[6U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta1);
  int32_t a_minus_b2 = simd_unit.coefficients[7U] - simd_unit.coefficients[5U];
  simd_unit.coefficients[5U] =
      simd_unit.coefficients[5U] + simd_unit.coefficients[7U];
  simd_unit.coefficients[7U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta1);
  return simd_unit;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta_00, int32_t zeta_01) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
          re[index], zeta_00, zeta_01);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)0U, (int32_t)3839961, (int32_t)-3628969);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)1U, (int32_t)-3881060, (int32_t)-3019102);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)2U, (int32_t)-1439742, (int32_t)-812732);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)3U, (int32_t)-1584928, (int32_t)1285669);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)4U, (int32_t)1341330, (int32_t)1315589);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)5U, (int32_t)-177440, (int32_t)-2409325);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)6U, (int32_t)-1851402, (int32_t)3159746);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)7U, (int32_t)-3553272, (int32_t)189548);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)8U, (int32_t)-1316856, (int32_t)759969);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)9U, (int32_t)-210977, (int32_t)2389356);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)10U, (int32_t)-3249728, (int32_t)1653064);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)11U, (int32_t)-8578, (int32_t)-3724342);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)12U, (int32_t)3958618, (int32_t)904516);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)13U, (int32_t)-1100098, (int32_t)44288);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)14U, (int32_t)3097992, (int32_t)508951);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)15U, (int32_t)264944, (int32_t)-3343383);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)16U, (int32_t)-1430430, (int32_t)1852771);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)17U, (int32_t)1349076, (int32_t)-381987);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)18U, (int32_t)-1308169, (int32_t)-22981);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)19U, (int32_t)-1228525, (int32_t)-671102);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)20U, (int32_t)-2477047, (int32_t)-411027);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)21U, (int32_t)-3693493, (int32_t)-2967645);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)22U, (int32_t)2715295, (int32_t)2147896);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)23U, (int32_t)-983419, (int32_t)3412210);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)24U, (int32_t)126922, (int32_t)-3632928);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)25U, (int32_t)-3157330, (int32_t)-3190144);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)26U, (int32_t)-1000202, (int32_t)-4083598);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)27U, (int32_t)1939314, (int32_t)-1257611);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)28U, (int32_t)-1585221, (int32_t)2176455);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)29U, (int32_t)3475950, (int32_t)-1452451);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)30U, (int32_t)-3041255, (int32_t)-3677745);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)31U, (int32_t)-1528703, (int32_t)-3930395);
}

static KRML_MUSTINLINE libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_unit,
    int32_t zeta) {
  int32_t a_minus_b = simd_unit.coefficients[4U] - simd_unit.coefficients[0U];
  simd_unit.coefficients[0U] =
      simd_unit.coefficients[0U] + simd_unit.coefficients[4U];
  simd_unit.coefficients[4U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, zeta);
  int32_t a_minus_b0 = simd_unit.coefficients[5U] - simd_unit.coefficients[1U];
  simd_unit.coefficients[1U] =
      simd_unit.coefficients[1U] + simd_unit.coefficients[5U];
  simd_unit.coefficients[5U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, zeta);
  int32_t a_minus_b1 = simd_unit.coefficients[6U] - simd_unit.coefficients[2U];
  simd_unit.coefficients[2U] =
      simd_unit.coefficients[2U] + simd_unit.coefficients[6U];
  simd_unit.coefficients[6U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, zeta);
  int32_t a_minus_b2 = simd_unit.coefficients[7U] - simd_unit.coefficients[3U];
  simd_unit.coefficients[3U] =
      simd_unit.coefficients[3U] + simd_unit.coefficients[7U];
  simd_unit.coefficients[7U] =
      libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, zeta);
  return simd_unit;
}

static inline void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re, size_t index,
    int32_t zeta1) {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
      libcrux_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
          re[index], zeta1);
  re[index] = uu____0;
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)0U, (int32_t)-2797779);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)1U, (int32_t)2071892);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)2U, (int32_t)-2556880);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)3U, (int32_t)3900724);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)4U, (int32_t)3881043);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)5U, (int32_t)954230);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)6U, (int32_t)531354);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)7U, (int32_t)811944);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)8U, (int32_t)3699596);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)9U, (int32_t)-1600420);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)10U, (int32_t)-2140649);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)11U, (int32_t)3507263);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)12U, (int32_t)-3821735);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)13U, (int32_t)3505694);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)14U, (int32_t)-1643818);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)15U, (int32_t)-1699267);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)16U, (int32_t)-539299);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)17U, (int32_t)2348700);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)18U, (int32_t)-300467);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)19U, (int32_t)3539968);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)20U, (int32_t)-2867647);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)21U, (int32_t)3574422);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)22U, (int32_t)-3043716);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)23U, (int32_t)-3861115);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)24U, (int32_t)3915439);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)25U, (int32_t)-2537516);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)26U, (int32_t)-3592148);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)27U, (int32_t)-1661693);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)28U, (int32_t)3530437);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)29U, (int32_t)3077325);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)30U, (int32_t)95776);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)31U, (int32_t)2706023);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_99(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)280005);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_1c(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)4010497);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_6b(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-19422);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_44(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1757237);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a8(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-3277672);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_1f(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1399561);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_95(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-3859737);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2118186);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2108549);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_e4(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2619752);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_de(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1119584);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_05(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-549488);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d9(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3585928);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3a(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-1079900);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1024112);
    re[j + (size_t)1U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)1U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)1U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2725464);
    re[j + (size_t)1U] = uu____1;
  }
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_99(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_1c(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_6b(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_44(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a8(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_1f(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_95(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_e4(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_de(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_05(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d9(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3a(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b0(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a0(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_990(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2680103);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3111497);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a80(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2884855);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_950(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)3119733);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2091905);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_de0(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-359251);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d90(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)2353451);
    re[j + (size_t)2U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)2U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)2U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)1826347);
    re[j + (size_t)2U] = uu____1;
  }
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_990(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_6b0(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a80(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_950(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a0(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_de0(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d90(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_3b1(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_991(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)4U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)466468);
    re[j + (size_t)4U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a81(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)4U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-876248);
    re[j + (size_t)4U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)4U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-777960);
    re[j + (size_t)4U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d91(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)4U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)4U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)237124);
    re[j + (size_t)4U] = uu____1;
  }
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_991(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_a81(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a1(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_d91(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_992(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)8U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)8U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-518909);
    re[j + (size_t)8U] = uu____1;
  }
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)8U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)8U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)-2608894);
    re[j + (size_t)8U] = uu____1;
  }
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_992(re);
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_7a2(re);
}

/**
A monomorphic instance of libcrux_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_993(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit a_minus_b =
        libcrux_ml_dsa_simd_portable_arithmetic_subtract(&re[j + (size_t)16U],
                                                         &re[j]);
    re[j] = libcrux_ml_dsa_simd_portable_arithmetic_add(&re[j],
                                                        &re[j + (size_t)16U]);
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____1 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            a_minus_b, (int32_t)25847);
    re[j + (size_t)16U] = uu____1;
  }
}

static KRML_MUSTINLINE void
libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *re) {
  libcrux_ml_dsa_simd_portable_invntt_outer_3_plus_993(re);
}

static inline void libcrux_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit re[32U],
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret[32U]) {
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(re);
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(re);
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)32U, re,
                   libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit),
               libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit);
       i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
        libcrux_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
            re[i0], (int32_t)41978);
    re[i0] = uu____0;
  }
  memcpy(ret, re,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
}

/**
This function found in impl {(libcrux_ml_dsa::simd::traits::Operations for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline void libcrux_ml_dsa_simd_portable_invert_ntt_montgomery_36(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_units[32U],
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret[32U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
      copy_of_simd_units[32U];
  memcpy(copy_of_simd_units, simd_units,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit ret0[32U];
  libcrux_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(copy_of_simd_units,
                                                            ret0);
  memcpy(ret, ret0,
         (size_t)32U *
             sizeof(libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit));
}

typedef struct uint8_t_x2_s {
  uint8_t fst;
  uint8_t snd;
} uint8_t_x2;

/**
A monomorphic instance of K.
with types uint8_t[4032size_t], uint8_t[1952size_t]

*/
typedef struct tuple_a0_s {
  uint8_t fst[4032U];
  uint8_t snd[1952U];
} tuple_a0;

/**
A monomorphic instance of libcrux_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit

*/
typedef struct libcrux_ml_dsa_polynomial_PolynomialRingElement_9b_s {
  libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit simd_units[32U];
} libcrux_ml_dsa_polynomial_PolynomialRingElement_9b;

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.ZERO_ff
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics

*/
static inline libcrux_ml_dsa_polynomial_PolynomialRingElement_9b
libcrux_ml_dsa_polynomial_ZERO_ff_ba(void) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b lit;
  lit.simd_units[0U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[1U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[2U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[3U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[4U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[5U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[6U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[7U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[8U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[9U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[10U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[11U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[12U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[13U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[14U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[15U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[16U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[17U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[18U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[19U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[20U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[21U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[22U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[23U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[24U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[25U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[26U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[27U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[28U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[29U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[30U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  lit.simd_units[31U] = libcrux_ml_dsa_simd_portable_ZERO_36();
  return lit;
}

typedef struct
    libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4_s {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b fst;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b snd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b thd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b f3;
} libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4;

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit with const generics

*/
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          core_slice___Slice_T___chunks(randomness, (size_t)24U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, core_slice_iter_Chunks);
  while (true) {
    Option_1b uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T__TraitClause_0___71__next(
            &iter, uint8_t, Option_1b);
    if (uu____0.tag == None) {
      break;
    } else {
      Eurydice_slice random_bytes = uu____0.f0;
      if (!done) {
        Eurydice_slice uu____1 = random_bytes;
        size_t sampled =
            libcrux_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_36(
                uu____1, Eurydice_array_to_subslice_from(
                             (size_t)263U, out, sampled_coefficients[0U],
                             int32_t, size_t));
        sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
        if (sampled_coefficients[0U] >=
            LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          done = true;
        }
      }
    }
  }
  return done;
}

/**
This function found in impl
{libcrux_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_dsa.polynomial.from_i32_array_ff
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics

*/
static inline libcrux_ml_dsa_polynomial_PolynomialRingElement_9b
libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(Eurydice_slice array) {
  core_slice_iter_Chunks array_chunks = core_slice___Slice_T___chunks(
      array, LIBCRUX_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT, int32_t,
      core_slice_iter_Chunks);
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b result =
      libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit uu____0 =
        libcrux_ml_dsa_simd_portable_from_coefficient_array_36(
            core_option__core__option__Option_T__TraitClause_0___unwrap(
                core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T__TraitClause_0___71__next(
                    &array_chunks, int32_t, Option_93),
                Eurydice_slice, Eurydice_slice));
    result.simd_units[i0] = uu____0;
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_four_ring_elements
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics

*/
static inline libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
libcrux_ml_dsa_sample_sample_four_ring_elements_ba(uint8_t seed0[34U],
                                                   uint16_t domain_separator0,
                                                   uint16_t domain_separator1,
                                                   uint16_t domain_seperator2,
                                                   uint16_t domain_separator3) {
  seed0[32U] = (uint8_t)domain_separator0;
  seed0[33U] = (uint8_t)((uint32_t)domain_separator0 >> 8U);
  uint8_t seed1[34U];
  memcpy(seed1, seed0, (size_t)34U * sizeof(uint8_t));
  seed1[32U] = (uint8_t)domain_separator1;
  seed1[33U] = (uint8_t)((uint32_t)domain_separator1 >> 8U);
  uint8_t seed2[34U];
  memcpy(seed2, seed0, (size_t)34U * sizeof(uint8_t));
  seed2[32U] = (uint8_t)domain_seperator2;
  seed2[33U] = (uint8_t)((uint32_t)domain_seperator2 >> 8U);
  uint8_t seed3[34U];
  memcpy(seed3, seed0, (size_t)34U * sizeof(uint8_t));
  seed3[32U] = (uint8_t)domain_separator3;
  seed3[33U] = (uint8_t)((uint32_t)domain_separator3 >> 8U);
  libcrux_ml_dsa_hash_functions_portable_Shake128X4 state =
      libcrux_ml_dsa_hash_functions_portable_init_absorb_ed(
          Eurydice_array_to_slice((size_t)34U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)34U, seed3, uint8_t));
  uint8_t randomness0[840U] = {0U};
  uint8_t randomness1[840U] = {0U};
  uint8_t randomness2[840U] = {0U};
  uint8_t randomness3[840U] = {0U};
  libcrux_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_ed(
      &state, randomness0, randomness1, randomness2, randomness3);
  int32_t coefficients0[263U] = {0U};
  int32_t coefficients1[263U] = {0U};
  int32_t coefficients2[263U] = {0U};
  int32_t coefficients3[263U] = {0U};
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
          Eurydice_array_to_slice((size_t)840U, randomness0, uint8_t),
          &sampled0, coefficients0);
  bool done1 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
          Eurydice_array_to_slice((size_t)840U, randomness1, uint8_t),
          &sampled1, coefficients1);
  bool done2 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
          Eurydice_array_to_slice((size_t)840U, randomness2, uint8_t),
          &sampled2, coefficients2);
  bool done3 =
      libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
          Eurydice_array_to_slice((size_t)840U, randomness3, uint8_t),
          &sampled3, coefficients3);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_168size_t__x4 randomnesses =
                libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_ed(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                              uint8_t),
                      &sampled0, coefficients0);
            }
            if (!done1) {
              done1 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                              uint8_t),
                      &sampled1, coefficients1);
            }
            if (!done2) {
              done2 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                              uint8_t),
                      &sampled2, coefficients2);
            }
            if (!done3) {
              done3 =
                  libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                      Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                              uint8_t),
                      &sampled3, coefficients3);
            }
          }
        } else {
          uint8_t_168size_t__x4 randomnesses =
              libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_ed(
                  &state);
          if (!done0) {
            done0 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                            uint8_t),
                    &sampled0, coefficients0);
          }
          if (!done1) {
            done1 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                            uint8_t),
                    &sampled1, coefficients1);
          }
          if (!done2) {
            done2 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                            uint8_t),
                    &sampled2, coefficients2);
          }
          if (!done3) {
            done3 =
                libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                    Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                            uint8_t),
                    &sampled3, coefficients3);
          }
        }
      } else {
        uint8_t_168size_t__x4 randomnesses =
            libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_ed(
                &state);
        if (!done0) {
          done0 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                          uint8_t),
                  &sampled0, coefficients0);
        }
        if (!done1) {
          done1 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                          uint8_t),
                  &sampled1, coefficients1);
        }
        if (!done2) {
          done2 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                          uint8_t),
                  &sampled2, coefficients2);
        }
        if (!done3) {
          done3 =
              libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                  Eurydice_array_to_slice((size_t)168U, randomnesses.f3,
                                          uint8_t),
                  &sampled3, coefficients3);
        }
      }
    } else {
      uint8_t_168size_t__x4 randomnesses =
          libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_ed(&state);
      if (!done0) {
        done0 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                Eurydice_array_to_slice((size_t)168U, randomnesses.fst,
                                        uint8_t),
                &sampled0, coefficients0);
      }
      if (!done1) {
        done1 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                Eurydice_array_to_slice((size_t)168U, randomnesses.snd,
                                        uint8_t),
                &sampled1, coefficients1);
      }
      if (!done2) {
        done2 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                Eurydice_array_to_slice((size_t)168U, randomnesses.thd,
                                        uint8_t),
                &sampled2, coefficients2);
      }
      if (!done3) {
        done3 =
            libcrux_ml_dsa_sample_rejection_sample_less_than_field_modulus_ba(
                Eurydice_array_to_slice((size_t)168U, randomnesses.f3, uint8_t),
                &sampled3, coefficients3);
      }
    }
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____0 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, coefficients0, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____1 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, coefficients1, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____2 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, coefficients2, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      lit;
  lit.fst = uu____0;
  lit.snd = uu____1;
  lit.thd = uu____2;
  lit.f3 = libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
      Eurydice_array_to_slice((size_t)263U, coefficients3, int32_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.update_matrix
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static inline void libcrux_ml_dsa_samplex4_update_matrix_2f(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b (*m)[5U], size_t i,
    size_t j, libcrux_ml_dsa_polynomial_PolynomialRingElement_9b v) {
  m[i][j] = v;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.matrix_A_4_by_4
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_matrix_A_4_by_4_2f(
    uint8_t seed[34U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret[6U][5U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b A[6U][5U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    A[i][0U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][1U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][2U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][3U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][4U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed[34U];
  memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed,
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)0U,
                                           four_ring_elements.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)1U,
                                           four_ring_elements.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)2U,
                                           four_ring_elements.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)3U,
                                           four_ring_elements.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed0[34U];
  memcpy(copy_of_seed0, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements0 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed0,
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)0U,
                                           four_ring_elements0.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)1U,
                                           four_ring_elements0.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)2U,
                                           four_ring_elements0.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)3U,
                                           four_ring_elements0.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed1[34U];
  memcpy(copy_of_seed1, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements1 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed1,
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)0U,
                                           four_ring_elements1.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)1U,
                                           four_ring_elements1.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)2U,
                                           four_ring_elements1.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)3U,
                                           four_ring_elements1.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed2[34U];
  memcpy(copy_of_seed2, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements2 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed2,
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)0U,
                                           four_ring_elements2.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)1U,
                                           four_ring_elements2.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)2U,
                                           four_ring_elements2.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)3U,
                                           four_ring_elements2.f3);
  memcpy(ret, A,
         (size_t)6U *
             sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.matrix_A_6_by_5
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_matrix_A_6_by_5_2f(
    uint8_t seed[34U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret[6U][5U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b A[6U][5U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    A[i][0U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][1U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][2U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][3U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][4U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed[34U];
  memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed,
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)0U,
                                           four_ring_elements.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)1U,
                                           four_ring_elements.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)2U,
                                           four_ring_elements.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)3U,
                                           four_ring_elements.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed0[34U];
  memcpy(copy_of_seed0, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements0 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed0,
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 2U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)4U,
                                           four_ring_elements0.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)0U,
                                           four_ring_elements0.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)1U,
                                           four_ring_elements0.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)2U,
                                           four_ring_elements0.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed1[34U];
  memcpy(copy_of_seed1, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements1 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed1,
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 1U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)3U,
                                           four_ring_elements1.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)4U,
                                           four_ring_elements1.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)0U,
                                           four_ring_elements1.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)1U,
                                           four_ring_elements1.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed2[34U];
  memcpy(copy_of_seed2, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements2 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed2,
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 0U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)2U,
                                           four_ring_elements2.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)3U,
                                           four_ring_elements2.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)4U,
                                           four_ring_elements2.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)0U,
                                           four_ring_elements2.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed3[34U];
  memcpy(copy_of_seed3, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements3 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed3,
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 4U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)1U,
                                           four_ring_elements3.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)2U,
                                           four_ring_elements3.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)3U,
                                           four_ring_elements3.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)4U,
                                           four_ring_elements3.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed4[34U];
  memcpy(copy_of_seed4, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements4 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed4,
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)0U,
                                           four_ring_elements4.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)1U,
                                           four_ring_elements4.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)2U,
                                           four_ring_elements4.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)3U,
                                           four_ring_elements4.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed5[34U];
  memcpy(copy_of_seed5, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements5 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed5,
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 2U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)4U,
                                           four_ring_elements5.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)0U,
                                           four_ring_elements5.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)1U,
                                           four_ring_elements5.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)2U,
                                           four_ring_elements5.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed6[34U];
  memcpy(copy_of_seed6, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements6 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed6,
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 6U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)3U,
                                           four_ring_elements6.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)4U,
                                           four_ring_elements6.snd);
  memcpy(ret, A,
         (size_t)6U *
             sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.matrix_A_8_by_7
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_matrix_A_8_by_7_2f(
    uint8_t seed[34U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret[6U][5U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b A[6U][5U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    A[i][0U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][1U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][2U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][3U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
    A[i][4U] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed[34U];
  memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed,
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)0U,
                                           four_ring_elements.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)1U,
                                           four_ring_elements.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)2U,
                                           four_ring_elements.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)3U,
                                           four_ring_elements.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed0[34U];
  memcpy(copy_of_seed0, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements0 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed0,
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(0U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 0U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)4U,
                                           four_ring_elements0.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)5U,
                                           four_ring_elements0.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)0U, (size_t)6U,
                                           four_ring_elements0.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)0U,
                                           four_ring_elements0.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed1[34U];
  memcpy(copy_of_seed1, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements1 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed1,
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 4U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)1U,
                                           four_ring_elements1.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)2U,
                                           four_ring_elements1.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)3U,
                                           four_ring_elements1.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)4U,
                                           four_ring_elements1.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed2[34U];
  memcpy(copy_of_seed2, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements2 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed2,
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(1U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 1U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)5U,
                                           four_ring_elements2.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)1U, (size_t)6U,
                                           four_ring_elements2.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)0U,
                                           four_ring_elements2.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)1U,
                                           four_ring_elements2.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed3[34U];
  memcpy(copy_of_seed3, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements3 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed3,
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 5U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)2U,
                                           four_ring_elements3.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)3U,
                                           four_ring_elements3.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)4U,
                                           four_ring_elements3.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)5U,
                                           four_ring_elements3.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed4[34U];
  memcpy(copy_of_seed4, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements4 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed4,
          libcrux_ml_dsa_samplex4_generate_domain_separator(2U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 2U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)2U, (size_t)6U,
                                           four_ring_elements4.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)0U,
                                           four_ring_elements4.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)1U,
                                           four_ring_elements4.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)2U,
                                           four_ring_elements4.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed5[34U];
  memcpy(copy_of_seed5, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements5 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed5,
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(3U, 6U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)3U,
                                           four_ring_elements5.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)4U,
                                           four_ring_elements5.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)5U,
                                           four_ring_elements5.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)3U, (size_t)6U,
                                           four_ring_elements5.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed6[34U];
  memcpy(copy_of_seed6, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements6 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed6,
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 3U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)0U,
                                           four_ring_elements6.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)1U,
                                           four_ring_elements6.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)2U,
                                           four_ring_elements6.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)3U,
                                           four_ring_elements6.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed7[34U];
  memcpy(copy_of_seed7, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements7 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed7,
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(4U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 0U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)4U,
                                           four_ring_elements7.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)5U,
                                           four_ring_elements7.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)4U, (size_t)6U,
                                           four_ring_elements7.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)0U,
                                           four_ring_elements7.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed8[34U];
  memcpy(copy_of_seed8, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements8 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed8,
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 4U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)1U,
                                           four_ring_elements8.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)2U,
                                           four_ring_elements8.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)3U,
                                           four_ring_elements8.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)4U,
                                           four_ring_elements8.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed9[34U];
  memcpy(copy_of_seed9, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements9 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed9,
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(5U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 1U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)5U,
                                           four_ring_elements9.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)5U, (size_t)6U,
                                           four_ring_elements9.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)0U,
                                           four_ring_elements9.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)1U,
                                           four_ring_elements9.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed10[34U];
  memcpy(copy_of_seed10, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements10 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed10,
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 2U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 5U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)2U,
                                           four_ring_elements10.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)3U,
                                           four_ring_elements10.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)4U,
                                           four_ring_elements10.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)5U,
                                           four_ring_elements10.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed11[34U];
  memcpy(copy_of_seed11, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements11 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed11,
          libcrux_ml_dsa_samplex4_generate_domain_separator(6U, 6U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 0U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 1U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 2U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)6U, (size_t)6U,
                                           four_ring_elements11.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)0U,
                                           four_ring_elements11.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)1U,
                                           four_ring_elements11.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)2U,
                                           four_ring_elements11.f3);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed12[34U];
  memcpy(copy_of_seed12, seed, (size_t)34U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four_ring_elements12 = libcrux_ml_dsa_sample_sample_four_ring_elements_ba(
          copy_of_seed12,
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 3U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 4U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 5U),
          libcrux_ml_dsa_samplex4_generate_domain_separator(7U, 6U));
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)3U,
                                           four_ring_elements12.fst);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)4U,
                                           four_ring_elements12.snd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)5U,
                                           four_ring_elements12.thd);
  libcrux_ml_dsa_samplex4_update_matrix_2f(A, (size_t)7U, (size_t)6U,
                                           four_ring_elements12.f3);
  memcpy(ret, A,
         (size_t)6U *
             sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.matrix_A
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_samplex4_matrix_A_2f(
    uint8_t seed[34U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret[6U][5U]) {
  uint8_t_x2 uu____0 = {.fst = (uint8_t)(size_t)6U, .snd = (uint8_t)(size_t)5U};
  switch (uu____0.fst) {
    case 4U: {
      switch (uu____0.snd) {
        case 4U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[34U];
          memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
          libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret0[6U][5U];
          libcrux_ml_dsa_samplex4_matrix_A_4_by_4_2f(copy_of_seed, ret0);
          memcpy(
              ret, ret0,
              (size_t)6U *
                  sizeof(
                      libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
          return;
        }
        default: {
        }
      }
      break;
    }
    case 6U: {
      switch (uu____0.snd) {
        case 5U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[34U];
          memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
          libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret0[6U][5U];
          libcrux_ml_dsa_samplex4_matrix_A_6_by_5_2f(copy_of_seed, ret0);
          memcpy(
              ret, ret0,
              (size_t)6U *
                  sizeof(
                      libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
          return;
        }
        default: {
        }
      }
      break;
    }
    case 8U: {
      switch (uu____0.snd) {
        case 7U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[34U];
          memcpy(copy_of_seed, seed, (size_t)34U * sizeof(uint8_t));
          libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret0[6U][5U];
          libcrux_ml_dsa_samplex4_matrix_A_8_by_7_2f(copy_of_seed, ret0);
          memcpy(
              ret, ret0,
              (size_t)6U *
                  sizeof(
                      libcrux_ml_dsa_polynomial_PolynomialRingElement_9b[5U]));
          return;
        }
        default: {
        }
      }
      break;
    }
    default: {
    }
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of K.
with types libcrux_ml_dsa_polynomial_PolynomialRingElement
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit[5size_t],
libcrux_ml_dsa_polynomial_PolynomialRingElement
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit[6size_t]

*/
typedef struct tuple_ce_s {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b fst[5U];
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b snd[6U];
} tuple_ce;

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit with const generics

*/
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_ba(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          core_slice___Slice_T___chunks(randomness, (size_t)4U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, core_slice_iter_Chunks);
  while (true) {
    Option_1b uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T__TraitClause_0___71__next(
            &iter, uint8_t, Option_1b);
    if (uu____0.tag == None) {
      break;
    } else {
      Eurydice_slice random_bytes = uu____0.f0;
      if (!done) {
        Eurydice_slice uu____1 = random_bytes;
        size_t sampled =
            libcrux_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_36(
                uu____1, Eurydice_array_to_subslice_from(
                             (size_t)263U, out, sampled_coefficients[0U],
                             int32_t, size_t));
        sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
        if (sampled_coefficients[0U] >=
            LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          done = true;
        }
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit with const generics

*/
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_ba(
    Eurydice_slice randomness, size_t *sampled_coefficients, int32_t *out) {
  bool done = false;
  core_slice_iter_Chunks iter =
      core_iter_traits_collect___core__iter__traits__collect__IntoIterator_for_I__1__into_iter(
          core_slice___Slice_T___chunks(randomness, (size_t)4U, uint8_t,
                                        core_slice_iter_Chunks),
          core_slice_iter_Chunks, core_slice_iter_Chunks);
  while (true) {
    Option_1b uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Chunks__a__T__TraitClause_0___71__next(
            &iter, uint8_t, Option_1b);
    if (uu____0.tag == None) {
      break;
    } else {
      Eurydice_slice random_bytes = uu____0.f0;
      if (!done) {
        Eurydice_slice uu____1 = random_bytes;
        size_t sampled =
            libcrux_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_36(
                uu____1, Eurydice_array_to_subslice_from(
                             (size_t)263U, out, sampled_coefficients[0U],
                             int32_t, size_t));
        sampled_coefficients[0U] = sampled_coefficients[0U] + sampled;
        if (sampled_coefficients[0U] >=
            LIBCRUX_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          done = true;
        }
      }
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.rejection_sample_less_than_eta
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ETA= 4
*/
static KRML_MUSTINLINE bool
libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
    Eurydice_slice randomness, size_t *sampled, int32_t *out) {
  return libcrux_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_ba(
      randomness, sampled, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.sample.sample_four_error_ring_elements
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ETA= 4
*/
static KRML_MUSTINLINE
    libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
    libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
        uint8_t seed_base[66U], uint16_t domain_separator0,
        uint16_t domain_separator1, uint16_t domain_seperator2,
        uint16_t domain_separator3) {
  uint8_t seed0[66U];
  memcpy(seed0, seed_base, (size_t)66U * sizeof(uint8_t));
  seed0[64U] = (uint8_t)domain_separator0;
  seed0[65U] = (uint8_t)((uint32_t)domain_separator0 >> 8U);
  uint8_t seed1[66U];
  memcpy(seed1, seed0, (size_t)66U * sizeof(uint8_t));
  seed1[64U] = (uint8_t)domain_separator1;
  seed1[65U] = (uint8_t)((uint32_t)domain_separator1 >> 8U);
  uint8_t seed2[66U];
  memcpy(seed2, seed0, (size_t)66U * sizeof(uint8_t));
  seed2[64U] = (uint8_t)domain_seperator2;
  seed2[65U] = (uint8_t)((uint32_t)domain_seperator2 >> 8U);
  uint8_t seed3[66U];
  memcpy(seed3, seed0, (size_t)66U * sizeof(uint8_t));
  seed3[64U] = (uint8_t)domain_separator3;
  seed3[65U] = (uint8_t)((uint32_t)domain_separator3 >> 8U);
  libcrux_ml_dsa_hash_functions_portable_Shake256X4 state =
      libcrux_ml_dsa_hash_functions_portable_init_absorb_x4_50(
          Eurydice_array_to_slice((size_t)66U, seed0, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed1, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed2, uint8_t),
          Eurydice_array_to_slice((size_t)66U, seed3, uint8_t));
  uint8_t_136size_t__x4 randomnesses0 =
      libcrux_ml_dsa_hash_functions_portable_squeeze_first_block_x4_50(&state);
  int32_t out0[263U] = {0U};
  int32_t out1[263U] = {0U};
  int32_t out2[263U] = {0U};
  int32_t out3[263U] = {0U};
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  bool done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
      Eurydice_array_to_slice((size_t)136U, randomnesses0.fst, uint8_t),
      &sampled0, out0);
  bool done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
      Eurydice_array_to_slice((size_t)136U, randomnesses0.snd, uint8_t),
      &sampled1, out1);
  bool done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
      Eurydice_array_to_slice((size_t)136U, randomnesses0.thd, uint8_t),
      &sampled2, out2);
  bool done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
      Eurydice_array_to_slice((size_t)136U, randomnesses0.f3, uint8_t),
      &sampled3, out3);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            uint8_t_136size_t__x4 randomnesses =
                libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4_50(
                    &state);
            if (!done0) {
              done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                  Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                          uint8_t),
                  &sampled0, out0);
            }
            if (!done1) {
              done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                  Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                          uint8_t),
                  &sampled1, out1);
            }
            if (!done2) {
              done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                  Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                          uint8_t),
                  &sampled2, out2);
            }
            if (!done3) {
              done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                  Eurydice_array_to_slice((size_t)136U, randomnesses.f3,
                                          uint8_t),
                  &sampled3, out3);
            }
          }
        } else {
          uint8_t_136size_t__x4 randomnesses =
              libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4_50(
                  &state);
          if (!done0) {
            done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                Eurydice_array_to_slice((size_t)136U, randomnesses.fst,
                                        uint8_t),
                &sampled0, out0);
          }
          if (!done1) {
            done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                Eurydice_array_to_slice((size_t)136U, randomnesses.snd,
                                        uint8_t),
                &sampled1, out1);
          }
          if (!done2) {
            done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                Eurydice_array_to_slice((size_t)136U, randomnesses.thd,
                                        uint8_t),
                &sampled2, out2);
          }
          if (!done3) {
            done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
                Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
                &sampled3, out3);
          }
        }
      } else {
        uint8_t_136size_t__x4 randomnesses =
            libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4_50(
                &state);
        if (!done0) {
          done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
              Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
              &sampled0, out0);
        }
        if (!done1) {
          done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
              Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
              &sampled1, out1);
        }
        if (!done2) {
          done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
              Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
              &sampled2, out2);
        }
        if (!done3) {
          done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
              Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
              &sampled3, out3);
        }
      }
    } else {
      uint8_t_136size_t__x4 randomnesses =
          libcrux_ml_dsa_hash_functions_portable_squeeze_next_block_x4_50(
              &state);
      if (!done0) {
        done0 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
            Eurydice_array_to_slice((size_t)136U, randomnesses.fst, uint8_t),
            &sampled0, out0);
      }
      if (!done1) {
        done1 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
            Eurydice_array_to_slice((size_t)136U, randomnesses.snd, uint8_t),
            &sampled1, out1);
      }
      if (!done2) {
        done2 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
            Eurydice_array_to_slice((size_t)136U, randomnesses.thd, uint8_t),
            &sampled2, out2);
      }
      if (!done3) {
        done3 = libcrux_ml_dsa_sample_rejection_sample_less_than_eta_73(
            Eurydice_array_to_slice((size_t)136U, randomnesses.f3, uint8_t),
            &sampled3, out3);
      }
    }
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____0 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, out0, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____1 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, out1, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b uu____2 =
      libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
          Eurydice_array_to_slice((size_t)263U, out2, int32_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      lit;
  lit.fst = uu____0;
  lit.snd = uu____1;
  lit.thd = uu____2;
  lit.f3 = libcrux_ml_dsa_polynomial_from_i32_array_ff_ba(
      Eurydice_array_to_slice((size_t)263U, out3, int32_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.sample_s1_and_s2_4_by_4
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ETA= 4
- S1_DIMENSION= 5
- S2_DIMENSION= 6
*/
static KRML_MUSTINLINE tuple_ce
libcrux_ml_dsa_samplex4_sample_s1_and_s2_4_by_4_fe(uint8_t seed_base[66U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    s1[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    s2[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base[66U];
  memcpy(copy_of_seed_base, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base, 0U, 1U, 2U, 3U);
  s1[0U] = four.fst;
  s1[1U] = four.snd;
  s1[2U] = four.thd;
  s1[3U] = four.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base0[66U];
  memcpy(copy_of_seed_base0, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four0 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base0, 4U, 5U, 6U, 7U);
  s2[0U] = four0.fst;
  s2[1U] = four0.snd;
  s2[2U] = four0.thd;
  s2[3U] = four0.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s1[5U];
  memcpy(
      copy_of_s1, s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s2[6U];
  memcpy(
      copy_of_s2, s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  tuple_ce lit;
  memcpy(
      lit.fst, copy_of_s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  memcpy(
      lit.snd, copy_of_s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.sample_s1_and_s2_5_by_6
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ETA= 4
- S1_DIMENSION= 5
- S2_DIMENSION= 6
*/
static KRML_MUSTINLINE tuple_ce
libcrux_ml_dsa_samplex4_sample_s1_and_s2_5_by_6_fe(uint8_t seed_base[66U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    s1[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    s2[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base[66U];
  memcpy(copy_of_seed_base, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base, 0U, 1U, 2U, 3U);
  s1[0U] = four.fst;
  s1[1U] = four.snd;
  s1[2U] = four.thd;
  s1[3U] = four.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base0[66U];
  memcpy(copy_of_seed_base0, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four0 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base0, 4U, 5U, 6U, 7U);
  s1[4U] = four0.fst;
  s2[0U] = four0.snd;
  s2[1U] = four0.thd;
  s2[2U] = four0.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base1[66U];
  memcpy(copy_of_seed_base1, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four1 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base1, 8U, 9U, 10U, 11U);
  s2[3U] = four1.fst;
  s2[4U] = four1.snd;
  s2[5U] = four1.thd;
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s1[5U];
  memcpy(
      copy_of_s1, s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s2[6U];
  memcpy(
      copy_of_s2, s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  tuple_ce lit;
  memcpy(
      lit.fst, copy_of_s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  memcpy(
      lit.snd, copy_of_s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.sample_s1_and_s2_7_by_8
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ETA= 4
- S1_DIMENSION= 5
- S2_DIMENSION= 6
*/
static KRML_MUSTINLINE tuple_ce
libcrux_ml_dsa_samplex4_sample_s1_and_s2_7_by_8_fe(uint8_t seed_base[66U]) {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    s1[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    s2[i] = libcrux_ml_dsa_polynomial_ZERO_ff_ba();
  }
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base[66U];
  memcpy(copy_of_seed_base, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base, 0U, 1U, 2U, 3U);
  s1[0U] = four.fst;
  s1[1U] = four.snd;
  s1[2U] = four.thd;
  s1[3U] = four.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base0[66U];
  memcpy(copy_of_seed_base0, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four0 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base0, 4U, 5U, 6U, 7U);
  s1[4U] = four0.fst;
  s1[5U] = four0.snd;
  s1[6U] = four0.thd;
  s2[0U] = four0.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base1[66U];
  memcpy(copy_of_seed_base1, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four1 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base1, 8U, 9U, 10U, 11U);
  s2[1U] = four1.fst;
  s2[2U] = four1.snd;
  s2[3U] = four1.thd;
  s2[4U] = four1.f3;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_seed_base2[66U];
  memcpy(copy_of_seed_base2, seed_base, (size_t)66U * sizeof(uint8_t));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_x4
      four2 = libcrux_ml_dsa_sample_sample_four_error_ring_elements_92(
          copy_of_seed_base2, 12U, 13U, 14U, 15U);
  s2[5U] = four2.fst;
  s2[6U] = four2.snd;
  s2[7U] = four2.thd;
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s1[5U];
  memcpy(
      copy_of_s1, s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s2[6U];
  memcpy(
      copy_of_s2, s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  tuple_ce lit;
  memcpy(
      lit.fst, copy_of_s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  memcpy(
      lit.snd, copy_of_s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ETA= 4
- S1_DIMENSION= 5
- S2_DIMENSION= 6
*/
static KRML_MUSTINLINE tuple_ce
libcrux_ml_dsa_samplex4_sample_s1_and_s2_fe(uint8_t seed[66U]) {
  uint8_t_x2 uu____0 = {.fst = (uint8_t)(size_t)5U, .snd = (uint8_t)(size_t)6U};
  switch (uu____0.fst) {
    case 4U: {
      switch (uu____0.snd) {
        case 4U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[66U];
          memcpy(copy_of_seed, seed, (size_t)66U * sizeof(uint8_t));
          return libcrux_ml_dsa_samplex4_sample_s1_and_s2_4_by_4_fe(
              copy_of_seed);
        }
        default: {
        }
      }
      break;
    }
    case 5U: {
      switch (uu____0.snd) {
        case 6U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[66U];
          memcpy(copy_of_seed, seed, (size_t)66U * sizeof(uint8_t));
          return libcrux_ml_dsa_samplex4_sample_s1_and_s2_5_by_6_fe(
              copy_of_seed);
        }
        default: {
        }
      }
      break;
    }
    case 7U: {
      switch (uu____0.snd) {
        case 8U: {
          /* Passing arrays by value in Rust generates a copy in C */
          uint8_t copy_of_seed[66U];
          memcpy(copy_of_seed, seed, (size_t)66U * sizeof(uint8_t));
          return libcrux_ml_dsa_samplex4_sample_s1_and_s2_7_by_8_fe(
              copy_of_seed);
        }
        default: {
        }
      }
      break;
    }
    default: {
    }
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "panic!");
  KRML_HOST_EXIT(255U);
}

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_ml_dsa.matrix.compute_As1_plus_s2
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_matrix_compute_As1_plus_s2_2f(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b (*A_as_ntt)[5U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b *s1,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b *s2,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b ret[6U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "@Array<libcrux_ml_dsa::polynomial::PolynomialRingElement<T@0>["
      "TraitClause@0, TraitClause@1], "
      "C@1>>[core::marker::Sized<@Array<libcrux_ml_dsa::polynomial::"
      "PolynomialRingElement<T@0>[TraitClause@0, TraitClause@1], C@1>>] "
      "enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

typedef struct
    libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_6size_t__x2_s {
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b fst[6U];
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b snd[6U];
} libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_6size_t__x2;

/**
A monomorphic instance of libcrux_ml_dsa.arithmetic.power2round_vector
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- DIMENSION= 6
*/
static KRML_MUSTINLINE
    libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_6size_t__x2
    libcrux_ml_dsa_arithmetic_power2round_vector_07(
        libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t[6U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "libcrux_ml_dsa::polynomial::PolynomialRingElement<T@0>[TraitClause@0, "
      "TraitClause@1]>[core::marker::Sized<libcrux_ml_dsa::polynomial::"
      "PolynomialRingElement<T@0>[TraitClause@0, TraitClause@1]>] "
      "enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit with const generics
- ROWS_IN_A= 6
- VERIFICATION_KEY_SIZE= 1952
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_verification_key_generate_serialized_2f(
    Eurydice_slice seed_for_A,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t1[6U],
    uint8_t ret[1952U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "libcrux_ml_dsa::polynomial::PolynomialRingElement<T@0>[TraitClause@0, "
      "TraitClause@1]>[core::marker::Sized<libcrux_ml_dsa::polynomial::"
      "PolynomialRingElement<T@0>[TraitClause@0, TraitClause@1]>] "
      "enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_hash_functions_portable_shake256_24(
    Eurydice_slice input, uint8_t *out) {
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)64U, out, uint8_t), input);
}

/**
This function found in impl {(libcrux_ml_dsa::hash_functions::shake256::DsaXof
for libcrux_ml_dsa::hash_functions::portable::Shake256)#2}
*/
/**
A monomorphic instance of libcrux_ml_dsa.hash_functions.portable.shake256_5c
with const generics
- OUTPUT_LENGTH= 64
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_hash_functions_portable_shake256_5c_24(Eurydice_slice input,
                                                      uint8_t *out) {
  libcrux_ml_dsa_hash_functions_portable_shake256_24(input, out);
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.error.serialize
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics
- ETA= 4
- OUTPUT_SIZE= 128
*/
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_error_serialize_ea(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b re, uint8_t ret[128U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "T@0>[TraitClause@0] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_ml_dsa.encoding.t0.serialize
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
with const generics

*/
static KRML_MUSTINLINE void libcrux_ml_dsa_encoding_t0_serialize_ba(
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b re, uint8_t ret[416U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"Error looking trait impl: "
      "core::slice::iter::{core::iter::traits::iterator::Iterator for "
      "core::slice::iter::Iter<\'a, T>[TraitClause@0]}#182<\'_, "
      "T@0>[TraitClause@0] enumerate\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of
libcrux_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake256 with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- SIGNING_KEY_SIZE= 4032
*/
static KRML_MUSTINLINE void
libcrux_ml_dsa_encoding_signing_key_generate_serialized_d2(
    Eurydice_slice seed_for_A, Eurydice_slice seed_for_signing,
    Eurydice_slice verification_key,
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s1[5U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s2[6U],
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t0[6U],
    uint8_t ret[4032U]) {
  uint8_t signing_key_serialized[4032U] = {0U};
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          signing_key_serialized, offset,
          offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t),
      seed_for_A, uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(
          signing_key_serialized, offset,
          offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE, uint8_t),
      seed_for_signing, uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE;
  uint8_t verification_key_hash[64U] = {0U};
  libcrux_ml_dsa_hash_functions_portable_shake256_5c_24(verification_key,
                                                        verification_key_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice2(
      signing_key_serialized, offset,
      offset + LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH,
      uint8_t);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)64U, verification_key_hash, uint8_t),
      uint8_t);
  offset = offset + LIBCRUX_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH;
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)5U, s1,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_9b),
               libcrux_ml_dsa_polynomial_PolynomialRingElement_9b);
       i++) {
    size_t _cloop_i = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b *ring_element =
        &s1[_cloop_i];
    Eurydice_slice uu____1 = Eurydice_array_to_subslice2(
        signing_key_serialized, offset, offset + (size_t)128U, uint8_t);
    uint8_t ret0[128U];
    libcrux_ml_dsa_encoding_error_serialize_ea(ring_element[0U], ret0);
    Eurydice_slice_copy(
        uu____1, Eurydice_array_to_slice((size_t)128U, ret0, uint8_t), uint8_t);
    offset = offset + (size_t)128U;
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)6U, s2,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_9b),
               libcrux_ml_dsa_polynomial_PolynomialRingElement_9b);
       i++) {
    size_t _cloop_i = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b *ring_element =
        &s2[_cloop_i];
    Eurydice_slice uu____2 = Eurydice_array_to_subslice2(
        signing_key_serialized, offset, offset + (size_t)128U, uint8_t);
    uint8_t ret0[128U];
    libcrux_ml_dsa_encoding_error_serialize_ea(ring_element[0U], ret0);
    Eurydice_slice_copy(
        uu____2, Eurydice_array_to_slice((size_t)128U, ret0, uint8_t), uint8_t);
    offset = offset + (size_t)128U;
  }
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)6U, t0,
                   libcrux_ml_dsa_polynomial_PolynomialRingElement_9b),
               libcrux_ml_dsa_polynomial_PolynomialRingElement_9b);
       i++) {
    size_t _cloop_i = i;
    libcrux_ml_dsa_polynomial_PolynomialRingElement_9b *ring_element =
        &t0[_cloop_i];
    Eurydice_slice uu____3 = Eurydice_array_to_subslice2(
        signing_key_serialized, offset,
        offset + LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE, uint8_t);
    uint8_t ret0[416U];
    libcrux_ml_dsa_encoding_t0_serialize_ba(ring_element[0U], ret0);
    Eurydice_slice_copy(
        uu____3, Eurydice_array_to_slice((size_t)416U, ret0, uint8_t), uint8_t);
    offset = offset + LIBCRUX_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
  }
  memcpy(ret, signing_key_serialized, (size_t)4032U * sizeof(uint8_t));
}

/**
 Generate a key pair.
*/
/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.generate_key_pair
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- SIGNING_KEY_SIZE= 4032
- VERIFICATION_KEY_SIZE= 1952
*/
static KRML_MUSTINLINE tuple_a0
libcrux_ml_dsa_ml_dsa_generic_generate_key_pair_5a(uint8_t randomness[32U]) {
  uint8_t seed_expanded0[128U] = {0U};
  libcrux_sha3_portable_incremental_Shake256Xof shake =
      libcrux_ml_dsa_hash_functions_portable_init_83();
  libcrux_ml_dsa_hash_functions_portable_absorb_83(
      &shake, Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  uint8_t buf[2U] = {(uint8_t)(size_t)6U, (uint8_t)(size_t)5U};
  libcrux_ml_dsa_hash_functions_portable_absorb_final_83(
      &shake, Eurydice_array_to_slice((size_t)2U, buf, uint8_t));
  libcrux_ml_dsa_hash_functions_portable_squeeze_83(
      &shake, Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)128U, seed_expanded0, uint8_t),
      LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_a = uu____0.fst;
  Eurydice_slice seed_expanded = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_error_vectors = uu____1.fst;
  Eurydice_slice seed_for_signing = uu____1.snd;
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b a_as_ntt[6U][5U];
  uint8_t ret[34U];
  libcrux_ml_dsa_utils_into_padded_array_b6(seed_for_a, ret);
  libcrux_ml_dsa_samplex4_matrix_A_2f(ret, a_as_ntt);
  uint8_t ret0[66U];
  libcrux_ml_dsa_utils_into_padded_array_20(seed_for_error_vectors, ret0);
  tuple_ce uu____2 = libcrux_ml_dsa_samplex4_sample_s1_and_s2_fe(ret0);
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s1[5U];
  memcpy(
      s1, uu____2.fst,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b s2[6U];
  memcpy(
      s2, uu____2.snd,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t[6U];
  libcrux_ml_dsa_matrix_compute_As1_plus_s2_2f(a_as_ntt, s1, s2, t);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_t[6U];
  memcpy(
      copy_of_t, t,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit_6size_t__x2
      uu____4 = libcrux_ml_dsa_arithmetic_power2round_vector_07(copy_of_t);
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t0[6U];
  memcpy(
      t0, uu____4.fst,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b t1[6U];
  memcpy(
      t1, uu____4.snd,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  Eurydice_slice uu____5 = seed_for_a;
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_t1[6U];
  memcpy(
      copy_of_t1, t1,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  uint8_t verification_key_serialized[1952U];
  libcrux_ml_dsa_encoding_verification_key_generate_serialized_2f(
      uu____5, copy_of_t1, verification_key_serialized);
  Eurydice_slice uu____7 = seed_for_a;
  Eurydice_slice uu____8 = seed_for_signing;
  Eurydice_slice uu____9 = Eurydice_array_to_slice(
      (size_t)1952U, verification_key_serialized, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s1[5U];
  memcpy(
      copy_of_s1, s1,
      (size_t)5U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_s2[6U];
  memcpy(
      copy_of_s2, s2,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_dsa_polynomial_PolynomialRingElement_9b copy_of_t0[6U];
  memcpy(
      copy_of_t0, t0,
      (size_t)6U * sizeof(libcrux_ml_dsa_polynomial_PolynomialRingElement_9b));
  uint8_t signing_key_serialized[4032U];
  libcrux_ml_dsa_encoding_signing_key_generate_serialized_d2(
      uu____7, uu____8, uu____9, copy_of_s1, copy_of_s2, copy_of_t0,
      signing_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key_serialized[4032U];
  memcpy(copy_of_signing_key_serialized, signing_key_serialized,
         (size_t)4032U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key_serialized[1952U];
  memcpy(copy_of_verification_key_serialized, verification_key_serialized,
         (size_t)1952U * sizeof(uint8_t));
  tuple_a0 lit;
  memcpy(lit.fst, copy_of_signing_key_serialized,
         (size_t)4032U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_verification_key_serialized,
         (size_t)1952U * sizeof(uint8_t));
  return lit;
}

/**
 Generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.instantiations.portable.generate_key_pair with
const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- SIGNING_KEY_SIZE= 4032
- VERIFICATION_KEY_SIZE= 1952
*/
static inline tuple_a0
libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_generate_key_pair_52(
    uint8_t randomness[32U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_generate_key_pair_5a(copy_of_randomness);
}

/**
 Generate an ML-DSA-65 Key Pair
*/
static inline libcrux_ml_dsa_ml_dsa_65_MLDSA65KeyPair
libcrux_ml_dsa_ml_dsa_65_portable_generate_key_pair(uint8_t randomness[32U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  tuple_a0 uu____1 =
      libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_generate_key_pair_52(
          copy_of_randomness);
  uint8_t signing_key[4032U];
  memcpy(signing_key, uu____1.fst, (size_t)4032U * sizeof(uint8_t));
  uint8_t verification_key[1952U];
  memcpy(verification_key, uu____1.snd, (size_t)1952U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_signing_key[4032U];
  memcpy(copy_of_signing_key, signing_key, (size_t)4032U * sizeof(uint8_t));
  libcrux_ml_dsa_types_MLDSASigningKey_22 uu____3 =
      libcrux_ml_dsa_types_new_9b_09(copy_of_signing_key);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_verification_key[1952U];
  memcpy(copy_of_verification_key, verification_key,
         (size_t)1952U * sizeof(uint8_t));
  libcrux_ml_dsa_ml_dsa_65_MLDSA65KeyPair lit;
  lit.signing_key = uu____3;
  lit.verification_key =
      libcrux_ml_dsa_types_new_66_97(copy_of_verification_key);
  return lit;
}

/**
A monomorphic instance of core.option.Option
with types libcrux_ml_dsa_pre_hash_DomainSeparationContext

*/
typedef struct Option_84_s {
  Option_08_tags tag;
  libcrux_ml_dsa_pre_hash_DomainSeparationContext f0;
} Option_84;

/**
 The internal signing API.

 If no `domain_separation_context` is supplied, it is assumed that
 `message` already contains the domain separation.
*/
/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.sign_internal
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- GAMMA1_EXPONENT= 19
- GAMMA2= 261888
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
- GAMMA1_RING_ELEMENT_SIZE= 640
- SIGNING_KEY_SIZE= 4032
- SIGNATURE_SIZE= 3309
*/
static KRML_MUSTINLINE Result_2e libcrux_ml_dsa_ml_dsa_generic_sign_internal_05(
    uint8_t *signing_key, Eurydice_slice message,
    Option_84 domain_separation_context, uint8_t randomness[32U]) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"TODO: TraitTypes "
      "core::result::{core::ops::try_trait::Try for core::result::Result<T, "
      "E>[TraitClause@0, TraitClause@1]}#26<T@0, T@1>[TraitClause@0, "
      "TraitClause@1]::Residual\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.sign
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_portable_Shake256X4 with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- GAMMA1_EXPONENT= 19
- GAMMA2= 261888
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
- GAMMA1_RING_ELEMENT_SIZE= 640
- SIGNING_KEY_SIZE= 4032
- SIGNATURE_SIZE= 3309
*/
static KRML_MUSTINLINE Result_2e libcrux_ml_dsa_ml_dsa_generic_sign_05(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  Result_a8 uu____0 = libcrux_ml_dsa_pre_hash_new_45(
      context, (CLITERAL(Option_3f){.tag = None}));
  Result_2e uu____1;
  if (uu____0.tag == Ok) {
    libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
        uu____0.val.case_Ok;
    libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context0 =
        domain_separation_context;
    uint8_t *uu____2 = signing_key;
    Eurydice_slice uu____3 = message;
    Option_84 uu____4 = {.tag = Some, .f0 = domain_separation_context0};
    /* Passing arrays by value in Rust generates a copy in C */
    uint8_t copy_of_randomness[32U];
    memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
    uu____1 = libcrux_ml_dsa_ml_dsa_generic_sign_internal_05(
        uu____2, uu____3, uu____4, copy_of_randomness);
  } else {
    uu____1 = (CLITERAL(Result_2e){
        .tag = Err,
        .val = {.case_Err = libcrux_ml_dsa_types_ContextTooLongError}});
  }
  return uu____1;
}

/**
 Sign.
*/
/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.instantiations.portable.sign with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- GAMMA1_EXPONENT= 19
- GAMMA2= 261888
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
- GAMMA1_RING_ELEMENT_SIZE= 640
- SIGNING_KEY_SIZE= 4032
- SIGNATURE_SIZE= 3309
*/
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_sign_f3(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_sign_05(uu____0, uu____1, uu____2,
                                               copy_of_randomness);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_2e libcrux_ml_dsa_ml_dsa_65_portable_sign(
    libcrux_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_ml_dsa_types_as_raw_9b_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_sign_f3(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.sign_pre_hashed
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_ml_dsa_pre_hash_SHAKE128_PH with const generics
- PH_DIGEST_LEN= 256
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- GAMMA1_EXPONENT= 19
- GAMMA2= 261888
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
- GAMMA1_RING_ELEMENT_SIZE= 640
- SIGNING_KEY_SIZE= 4032
- SIGNATURE_SIZE= 3309
*/
static KRML_MUSTINLINE Result_2e
libcrux_ml_dsa_ml_dsa_generic_sign_pre_hashed_0d(uint8_t *signing_key,
                                                 Eurydice_slice message,
                                                 Eurydice_slice context,
                                                 uint8_t randomness[32U]) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "Eurydice error: Failure(\"expression_of_operand Constant: "
                    "TraitClause@13OID\")\n");
  KRML_HOST_EXIT(255U);
}

/**
 Sign (pre-hashed).
*/
/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.instantiations.portable.sign_pre_hashed_shake128
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- ETA= 4
- ERROR_RING_ELEMENT_SIZE= 128
- GAMMA1_EXPONENT= 19
- GAMMA2= 261888
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
- GAMMA1_RING_ELEMENT_SIZE= 640
- SIGNING_KEY_SIZE= 4032
- SIGNATURE_SIZE= 3309
*/
static inline Result_2e
libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_sign_pre_hashed_shake128_f3(
    uint8_t *signing_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t randomness[32U]) {
  uint8_t *uu____0 = signing_key;
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_sign_pre_hashed_0d(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_2e
libcrux_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    libcrux_ml_dsa_types_MLDSASigningKey_22 *signing_key,
    Eurydice_slice message, Eurydice_slice context, uint8_t randomness[32U]) {
  uint8_t *uu____0 = libcrux_ml_dsa_types_as_raw_9b_09(signing_key);
  Eurydice_slice uu____1 = message;
  Eurydice_slice uu____2 = context;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_sign_pre_hashed_shake128_f3(
      uu____0, uu____1, uu____2, copy_of_randomness);
}

/**
 The internal verification API.

 If no `domain_separation_context` is supplied, it is assumed that
 `message` already contains the domain separation.
*/
/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.verify_internal
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- SIGNATURE_SIZE= 3309
- VERIFICATION_KEY_SIZE= 1952
- GAMMA1_EXPONENT= 19
- GAMMA1_RING_ELEMENT_SIZE= 640
- GAMMA2= 261888
- BETA= 196
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
*/
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_ml_dsa_generic_verify_internal_99(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Option_84 domain_separation_context, uint8_t *signature_serialized) {
  KRML_HOST_EPRINTF(
      "KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
      "Eurydice error: Failure(\"TODO: TraitTypes "
      "core::result::{core::ops::try_trait::Try for core::result::Result<T, "
      "E>[TraitClause@0, TraitClause@1]}#26<T@0, T@1>[TraitClause@0, "
      "TraitClause@1]::Residual\")\n");
  KRML_HOST_EXIT(255U);
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.verify
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- SIGNATURE_SIZE= 3309
- VERIFICATION_KEY_SIZE= 1952
- GAMMA1_EXPONENT= 19
- GAMMA1_RING_ELEMENT_SIZE= 640
- GAMMA2= 261888
- BETA= 196
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
*/
static KRML_MUSTINLINE Result_41 libcrux_ml_dsa_ml_dsa_generic_verify_99(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  Result_a8 uu____0 = libcrux_ml_dsa_pre_hash_new_45(
      context, (CLITERAL(Option_3f){.tag = None}));
  Result_41 uu____1;
  if (uu____0.tag == Ok) {
    libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context =
        uu____0.val.case_Ok;
    libcrux_ml_dsa_pre_hash_DomainSeparationContext domain_separation_context0 =
        domain_separation_context;
    uu____1 = libcrux_ml_dsa_ml_dsa_generic_verify_internal_99(
        verification_key_serialized, message,
        (CLITERAL(Option_84){.tag = Some, .f0 = domain_separation_context0}),
        signature_serialized);
  } else {
    uu____1 = (CLITERAL(Result_41){
        .tag = Err,
        .f0 = libcrux_ml_dsa_types_VerificationContextTooLongError});
  }
  return uu____1;
}

/**
 Verify.
*/
/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.instantiations.portable.verify with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- SIGNATURE_SIZE= 3309
- VERIFICATION_KEY_SIZE= 1952
- GAMMA1_EXPONENT= 19
- GAMMA1_RING_ELEMENT_SIZE= 640
- GAMMA2= 261888
- BETA= 196
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
*/
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_verify_01(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_verify_99(verification_key, message,
                                                 context, signature);
}

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_41 libcrux_ml_dsa_ml_dsa_65_portable_verify(
    libcrux_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_verify_01(
      libcrux_ml_dsa_types_as_raw_66_97(verification_key), message, context,
      libcrux_ml_dsa_types_as_raw_8f_fa(signature));
}

/**
A monomorphic instance of libcrux_ml_dsa.ml_dsa_generic.verify_pre_hashed
with types libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit,
libcrux_ml_dsa_hash_functions_portable_Shake128,
libcrux_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_ml_dsa_hash_functions_portable_Shake256,
libcrux_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_ml_dsa_pre_hash_SHAKE128_PH with const generics
- PH_DIGEST_LEN= 256
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- SIGNATURE_SIZE= 3309
- VERIFICATION_KEY_SIZE= 1952
- GAMMA1_EXPONENT= 19
- GAMMA1_RING_ELEMENT_SIZE= 640
- GAMMA2= 261888
- BETA= 196
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
*/
static KRML_MUSTINLINE Result_41
libcrux_ml_dsa_ml_dsa_generic_verify_pre_hashed_ae(
    uint8_t *verification_key_serialized, Eurydice_slice message,
    Eurydice_slice context, uint8_t *signature_serialized) {
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                    "Eurydice error: Failure(\"expression_of_operand Constant: "
                    "TraitClause@11OID\")\n");
  KRML_HOST_EXIT(255U);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
/**
A monomorphic instance of
libcrux_ml_dsa.ml_dsa_generic.instantiations.portable.verify_pre_hashed_shake128
with const generics
- ROWS_IN_A= 6
- COLUMNS_IN_A= 5
- SIGNATURE_SIZE= 3309
- VERIFICATION_KEY_SIZE= 1952
- GAMMA1_EXPONENT= 19
- GAMMA1_RING_ELEMENT_SIZE= 640
- GAMMA2= 261888
- BETA= 196
- COMMITMENT_RING_ELEMENT_SIZE= 128
- COMMITMENT_VECTOR_SIZE= 768
- COMMITMENT_HASH_SIZE= 48
- ONES_IN_VERIFIER_CHALLENGE= 49
- MAX_ONES_IN_HINT= 55
*/
static inline Result_41
libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_verify_pre_hashed_shake128_01(
    uint8_t *verification_key, Eurydice_slice message, Eurydice_slice context,
    uint8_t *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_verify_pre_hashed_ae(
      verification_key, message, context, signature);
}

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
static inline Result_41
libcrux_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    libcrux_ml_dsa_types_MLDSAVerificationKey_ea *verification_key,
    Eurydice_slice message, Eurydice_slice context,
    libcrux_ml_dsa_ml_dsa_65_MLDSA65Signature *signature) {
  return libcrux_ml_dsa_ml_dsa_generic_instantiations_portable_verify_pre_hashed_shake128_01(
      libcrux_ml_dsa_types_as_raw_66_97(verification_key), message, context,
      libcrux_ml_dsa_types_as_raw_8f_fa(signature));
}

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_ml_dsa::pre_hash::DomainSeparationContext<'a>#1}
*/
static inline Option_3f libcrux_ml_dsa_pre_hash_pre_hash_oid_45(
    libcrux_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return self->pre_hash_oid;
}

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_ml_dsa::pre_hash::DomainSeparationContext<'a>#1}
*/
static inline Eurydice_slice libcrux_ml_dsa_pre_hash_context_45(
    libcrux_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return self->context;
}

#define LIBCRUX_ML_DSA_PRE_HASH_PRE_HASH_OID_LEN ((size_t)11U)

typedef uint8_t libcrux_ml_dsa_pre_hash_PreHashOID[11U];

/**
This function found in impl
{(core::convert::From<libcrux_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_ml_dsa::types::SigningError)#2}
*/
static inline libcrux_ml_dsa_types_SigningError libcrux_ml_dsa_pre_hash_from_4b(
    libcrux_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_ml_dsa_types_ContextTooLongError;
}

/**
This function found in impl
{(core::convert::From<libcrux_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_ml_dsa::types::VerificationError)#3}
*/
static inline libcrux_ml_dsa_types_VerificationError
libcrux_ml_dsa_pre_hash_from_b6(
    libcrux_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_ml_dsa_types_VerificationContextTooLongError;
}

static const uint8_t
    libcrux_ml_dsa_pre_hash___libcrux_ml_dsa__pre_hash__PreHash_256__usize__for_libcrux_ml_dsa__pre_hash__SHAKE128_PH___OID
        [11U] = {6U, 9U, 96U, 134U, 72U, 1U, 101U, 3U, 4U, 2U, 11U};

static KRML_MUSTINLINE bool libcrux_ml_dsa_sample_inside_out_shuffle(
    Eurydice_slice randomness, size_t *out_index, uint64_t *signs,
    int32_t *result) {
  bool done = false;
  core_slice_iter_Iter iter =
      core_slice_iter___core__iter__traits__collect__IntoIterator_for___a___Slice_T____1__into_iter(
          randomness, uint8_t, core_slice_iter_Iter);
  while (true) {
    Option_3f uu____0 =
        core_slice_iter___core__iter__traits__iterator__Iterator_for_core__slice__iter__Iter__a__T__TraitClause_0___182__next(
            &iter, uint8_t, Option_3f);
    if (uu____0.tag == None) {
      break;
    } else {
      uint8_t *byte = uu____0.f0;
      if (!done) {
        size_t sample_at = (size_t)byte[0U];
        if (sample_at <= out_index[0U]) {
          result[out_index[0U]] = result[sample_at];
          out_index[0U] = out_index[0U] + (size_t)1U;
          result[sample_at] =
              (int32_t)1 - (int32_t)2 * (int32_t)(signs[0U] & 1ULL);
          signs[0U] = signs[0U] >> 1U;
          size_t uu____1 = out_index[0U];
          done = uu____1 ==
                 Eurydice_slice_len(
                     Eurydice_array_to_slice((size_t)256U, result, int32_t),
                     int32_t);
        } else {
          size_t uu____2 = out_index[0U];
          done = uu____2 ==
                 Eurydice_slice_len(
                     Eurydice_array_to_slice((size_t)256U, result, int32_t),
                     int32_t);
        }
      }
    }
  }
  return done;
}

static KRML_MUSTINLINE void libcrux_ml_dsa_sample_update_seed(
    uint8_t seed[66U], uint16_t *domain_separator, uint8_t ret[66U]) {
  seed[64U] = (uint8_t)domain_separator[0U];
  seed[65U] = (uint8_t)((uint32_t)domain_separator[0U] >> 8U);
  domain_separator[0U] = (uint32_t)domain_separator[0U] + 1U;
  memcpy(ret, seed, (size_t)66U * sizeof(uint8_t));
}

typedef struct int32_t_x2_s {
  int32_t fst;
  int32_t snd;
} int32_t_x2;

static KRML_MUSTINLINE int32_t_x2
libcrux_ml_dsa_simd_portable_arithmetic_power2round_element(int32_t t) {
  int32_t t2 = t + (t >> 31U & LIBCRUX_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t t1 =
      (t2 - (int32_t)1 +
       ((int32_t)1
        << (uint32_t)(LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                      (size_t)1U))) >>
      (uint32_t)LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T;
  int32_t t0 =
      t2 - (t1 << (uint32_t)LIBCRUX_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T);
  return (CLITERAL(int32_t_x2){.fst = t0, .snd = t1});
}

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  ((int32_t)4)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1                     \
    << 1U) -                                                                                                    \
   (int32_t)1)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK \
  ((LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1                     \
    << 1U) -                                                                                                    \
   (int32_t)1)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)1 << 17U)

#define LIBCRUX_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)1 << 19U)

/**
This function found in impl {(core::clone::Clone for
libcrux_ml_dsa::simd::portable::vector_type::PortableSIMDUnit)}
*/
static inline libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit
libcrux_ml_dsa_simd_portable_vector_type_clone_ae(
    libcrux_ml_dsa_simd_portable_vector_type_PortableSIMDUnit *self) {
  return self[0U];
}

/**
This function found in impl {(core::fmt::Debug for
libcrux_ml_dsa::types::SigningError)#7}
*/
static inline Result_a9 libcrux_ml_dsa_types_fmt_16(
    libcrux_ml_dsa_types_SigningError *self, core_fmt_Formatter *f) {
  core_fmt_Formatter *uu____0 = f;
  Prims_string uu____1;
  switch (self[0U]) {
    case libcrux_ml_dsa_types_RejectionSamplingError: {
      uu____1 = "RejectionSamplingError";
      break;
    }
    case libcrux_ml_dsa_types_ContextTooLongError: {
      uu____1 = "ContextTooLongError";
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return core_fmt__core__fmt__Formatter__a__9__write_str(uu____0, uu____1);
}

/**
This function found in impl {(core::fmt::Debug for
libcrux_ml_dsa::types::VerificationError)#6}
*/
static inline Result_a9 libcrux_ml_dsa_types_fmt_7e(
    libcrux_ml_dsa_types_VerificationError *self, core_fmt_Formatter *f) {
  core_fmt_Formatter *uu____0 = f;
  Prims_string uu____1;
  switch (self[0U]) {
    case libcrux_ml_dsa_types_MalformedHintError: {
      uu____1 = "MalformedHintError";
      break;
    }
    case libcrux_ml_dsa_types_SignerResponseExceedsBoundError: {
      uu____1 = "SignerResponseExceedsBoundError";
      break;
    }
    case libcrux_ml_dsa_types_CommitmentHashesDontMatchError: {
      uu____1 = "CommitmentHashesDontMatchError";
      break;
    }
    case libcrux_ml_dsa_types_VerificationContextTooLongError: {
      uu____1 = "VerificationContextTooLongError";
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return core_fmt__core__fmt__Formatter__a__9__write_str(uu____0, uu____1);
}

typedef int32_t libcrux_ml_dsa_simd_traits_FieldElementTimesMontgomeryR;

typedef int32_t libcrux_ml_dsa_simd_portable_vector_type_FieldElement;

typedef Result_a8 libcrux_ml_dsa_pre_hash_PreHashResult;

typedef struct libcrux_ml_dsa_hash_functions_portable_Shake128_s {
} libcrux_ml_dsa_hash_functions_portable_Shake128;

#if defined(__cplusplus)
}
#endif

#define __libcrux_mldsa65_portable_H_DEFINED
#endif
