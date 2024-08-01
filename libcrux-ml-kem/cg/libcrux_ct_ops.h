/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: ab466d75991f78bb7925bf97c8ee9874f67074f5
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 311466858468504a1c6f5510661dc1f0adc332ba
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
  uint16_t uu____0 = value0;
  uint16_t result = (((uint32_t)uu____0 |
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
    uint8_t uu____0 =
        Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *, uint8_t);
    r = (uint32_t)r |
        ((uint32_t)uu____0 ^
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
    uint8_t uu____0 =
        (uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *, uint8_t) &
        (uint32_t)mask;
    uint8_t *uu____1 =
        &Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *, uint8_t);
    out[i0] = (uint32_t)uu____0 | ((uint32_t)uu____1[0U] & (uint32_t)~mask);
  }
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_NOINLINE void
libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_ct(lhs, rhs, selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
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
