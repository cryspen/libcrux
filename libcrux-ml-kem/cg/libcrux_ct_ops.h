/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: 67f4341506300372fba9cb8de070234935839cb7
 * Karamel: f9cdef256a2b88282398a609847b34dd8c9cf3e3
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 06b02e72e21705b53062d5988d3233715af43ad2
 */

#ifndef __libcrux_ct_ops_H
#define __libcrux_ct_ops_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

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

static inline uint8_t libcrux_ml_kem_constant_time_ops_compare(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  uint8_t r = 0U;
  for (size_t i = (size_t)0U;
       i < core_slice___Slice_T___len(lhs, uint8_t, size_t); i++) {
    size_t i0 = i;
    r = (uint32_t)r |
        ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *, uint8_t) ^
         (uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *, uint8_t));
  }
  return libcrux_ml_kem_constant_time_ops_is_non_zero(r);
}

static KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  return libcrux_ml_kem_constant_time_ops_compare(lhs, rhs);
}

static inline void libcrux_ml_kem_constant_time_ops_select_ct(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  uint8_t mask = core_num__u8_6__wrapping_sub(
      libcrux_ml_kem_constant_time_ops_is_non_zero(selector), 1U);
  uint8_t out[32U] = {0U};
  for (size_t i = (size_t)0U; i < LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE;
       i++) {
    size_t i0 = i;
    out[i0] =
        ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *, uint8_t) &
         (uint32_t)mask) |
        ((uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *, uint8_t) &
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
