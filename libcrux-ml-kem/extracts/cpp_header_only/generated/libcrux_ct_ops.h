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
 * Libcrux: fdf48700ae0f91db392ad5685a16b2393dab4c86
 */

#ifndef libcrux_ct_ops_H
#define libcrux_ct_ops_H

#include "eurydice_glue.h"
#include "libcrux_mlkem_core.h"

/**
 Return 1 if `value` is not zero and 0 otherwise.
*/
static KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_inz(uint8_t value) {
  uint16_t value0 = (uint16_t)value;
  uint8_t result =
      (uint8_t)((uint32_t)core_num__u16__wrapping_add(~value0, 1U) >> 8U);
  return (uint32_t)result & 1U;
}

static KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_is_non_zero(uint8_t value) {
  return libcrux_ml_kem_constant_time_ops_inz(value);
}

/**
 Return 1 if the bytes of `lhs` and `rhs` do not exactly
 match and 0 otherwise.
*/
static KRML_NOINLINE uint8_t libcrux_ml_kem_constant_time_ops_compare(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  uint8_t r = 0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(lhs, uint8_t); i++) {
    size_t i0 = i;
    uint8_t nr = (uint32_t)r |
                 ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) ^
                  (uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *));
    r = nr;
  }
  return libcrux_ml_kem_constant_time_ops_is_non_zero(r);
}

static KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  return libcrux_ml_kem_constant_time_ops_compare(lhs, rhs);
}

/**
 If `selector` is not zero, return the bytes in `rhs`; return the bytes in
 `lhs` otherwise.
*/
static KRML_NOINLINE Eurydice_arr_600
libcrux_ml_kem_constant_time_ops_select_ct(Eurydice_slice lhs,
                                           Eurydice_slice rhs,
                                           uint8_t selector) {
  uint8_t mask = core_num__u8__wrapping_sub(
      libcrux_ml_kem_constant_time_ops_is_non_zero(selector), 1U);
  Eurydice_arr_600 out = {{0U}};
  for (size_t i = (size_t)0U; i < LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE;
       i++) {
    size_t i0 = i;
    uint8_t outi =
        ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) &
         (uint32_t)mask) |
        ((uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *) &
         (uint32_t)~mask);
    out.data[i0] = outi;
  }
  return out;
}

static KRML_NOINLINE Eurydice_arr_600
libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector) {
  return libcrux_ml_kem_constant_time_ops_select_ct(lhs, rhs, selector);
}

static KRML_NOINLINE Eurydice_arr_600
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s) {
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          lhs_c, rhs_c);
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      lhs_s, rhs_s, selector);
}

#define libcrux_ct_ops_H_DEFINED
#endif /* libcrux_ct_ops_H */
