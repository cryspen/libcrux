/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 6b5e110342a771a3e1c739b10294b1778e4be8b4
 * Eurydice: 31be7d65ca5d6acdacfb33652e478d24dd85c1cb
 * Karamel: 3205d3365ea2790b02368f79fcee38e38d0b5908
 * F*: 86be6d1083452ef1a2c8991bcf72e36e8f6f5efb
 * Libcrux: 33d08ed8cc74e9d1b2c29d754e70a5b2998bd6e5
 */

#ifndef __libcrux_ct_ops_H
#define __libcrux_ct_ops_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

/**
 Return 1 if `value` is not zero and 0 otherwise.
*/
static inline uint8_t libcrux_ml_kem_constant_time_ops_inz(uint8_t value) {
  uint16_t value0 = (uint16_t)value;
  uint16_t result = (((uint32_t)value0 |
                      (uint32_t)core_num__u16_7__wrapping_add(~value0, 1U)) &
                     0xFFFFU) >>
                        8U &
                    1U;
  return (uint8_t)result;
}

static KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_is_non_zero(uint8_t value) {
  return libcrux_ml_kem_constant_time_ops_inz(value);
}

/**
 Return 1 if the bytes of `lhs` and `rhs` do not exactly
 match and 0 otherwise.
*/
static inline uint8_t libcrux_ml_kem_constant_time_ops_compare(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  uint8_t r = 0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(lhs, uint8_t); i++) {
    size_t i0 = i;
    r = (uint32_t)r |
        ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) ^
         (uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *));
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
static inline void libcrux_ml_kem_constant_time_ops_select_ct(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  uint8_t mask = core_num__u8_6__wrapping_sub(
      libcrux_ml_kem_constant_time_ops_is_non_zero(selector), 1U);
  uint8_t out[32U] = {0U};
  for (size_t i = (size_t)0U; i < LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE;
       i++) {
    size_t i0 = i;
    out[i0] = ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) &
               (uint32_t)mask) |
              ((uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *) &
               (uint32_t)~mask);
  }
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_NOINLINE void
libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  libcrux_ml_kem_constant_time_ops_select_ct(lhs, rhs, selector, ret);
}

static inline void
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s, uint8_t ret[32U]) {
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          lhs_c, rhs_c);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      lhs_s, rhs_s, selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

#if defined(__cplusplus)
}
#endif

#define __libcrux_ct_ops_H_DEFINED
#endif
