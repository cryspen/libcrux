/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 920e78bb15250348a7a7a938e8023148e0a249bf
 * Eurydice: 4d6cf6308cb714aadcd1df0ba5f71977ec6c4a99
 * Karamel: 65aab550cf3ba36d52ae6ad1ad962bb573406395
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: c9c098bdea22047a1eb811ddf3468543855da224
 */

#include "internal/libcrux_core.h"

static uint8_t inz(uint8_t value) {
  uint16_t value0 = (uint16_t)value;
  uint16_t uu____0 = value0;
  uint16_t result = (((uint32_t)uu____0 |
                      (uint32_t)core_num__u16_7__wrapping_add(~value0, 1U)) &
                     0xFFFFU) >>
                        8U &
                    1U;
  return (uint8_t)result;
}

static KRML_NOINLINE uint8_t is_non_zero(uint8_t value) { return inz(value); }

static uint8_t compare(Eurydice_slice lhs, Eurydice_slice rhs) {
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
  return is_non_zero(r);
}

KRML_NOINLINE uint8_t
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs) {
  return compare(lhs, rhs);
}

static void select_ct(Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
                      uint8_t ret[32U]) {
  uint8_t mask = core_num__u8_6__wrapping_sub(is_non_zero(selector), 1U);
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

KRML_NOINLINE void
libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  select_ct(lhs, rhs, selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
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

libcrux_ml_kem_types_MlKemPublicKey____1568size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1568size_t(
    uint8_t value[1568U]) {
  uint8_t uu____0[1568U];
  memcpy(uu____0, value, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey____1568size_t lit;
  memcpy(lit.value, uu____0, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___3168size_t_1568size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem1024_MlKem1024KeyPair){.sk = sk, .pk = pk});
}

libcrux_ml_kem_types_MlKemPrivateKey____3168size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___3168size_t(
    uint8_t value[3168U]) {
  uint8_t uu____0[3168U];
  memcpy(uu____0, value, (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____3168size_t lit;
  memcpy(lit.value, uu____0, (size_t)3168U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1568size_t(
    uint8_t value[1568U]) {
  uint8_t uu____0[1568U];
  memcpy(uu____0, value, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext lit;
  memcpy(lit.value, uu____0, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1568size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *self) {
  return self->value;
}

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1568size_t(
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1568U, self->value, uint8_t,
                                 Eurydice_slice);
}

void libcrux_ml_kem_utils_into_padded_array___1600size_t(Eurydice_slice slice,
                                                         uint8_t ret[1600U]) {
  uint8_t out[1600U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)1600U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)1600U * sizeof(uint8_t));
}

libcrux_ml_kem_types_MlKemPublicKey____1184size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___1184size_t(
    uint8_t value[1184U]) {
  uint8_t uu____0[1184U];
  memcpy(uu____0, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey____1184size_t lit;
  memcpy(lit.value, uu____0, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___2400size_t_1184size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t pk) {
  return (
      CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk, .pk = pk});
}

libcrux_ml_kem_types_MlKemPrivateKey____2400size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___2400size_t(
    uint8_t value[2400U]) {
  uint8_t uu____0[2400U];
  memcpy(uu____0, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____2400size_t lit;
  memcpy(lit.value, uu____0, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_mlkem768_MlKem768Ciphertext
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___1088size_t(
    uint8_t value[1088U]) {
  uint8_t uu____0[1088U];
  memcpy(uu____0, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, uu____0, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___1184size_t(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *self) {
  return self->value;
}

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___1088size_t(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1088U, self->value, uint8_t,
                                 Eurydice_slice);
}

void libcrux_ml_kem_utils_into_padded_array___1120size_t(Eurydice_slice slice,
                                                         uint8_t ret[1120U]) {
  uint8_t out[1120U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)1120U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)1120U * sizeof(uint8_t));
}

libcrux_ml_kem_types_MlKemPublicKey____800size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPublicKey_SIZE___14__from___800size_t(
    uint8_t value[800U]) {
  uint8_t uu____0[800U];
  memcpy(uu____0, value, (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey____800size_t lit;
  memcpy(lit.value, uu____0, (size_t)800U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemKeyPair_PRIVATE_KEY_SIZE__PUBLIC_KEY_SIZE___from___1632size_t_800size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t sk,
    libcrux_ml_kem_types_MlKemPublicKey____800size_t pk) {
  return (CLITERAL(libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t){
      .sk = sk, .pk = pk});
}

libcrux_ml_kem_types_MlKemPrivateKey____1632size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemPrivateKey_SIZE___8__from___1632size_t(
    uint8_t value[1632U]) {
  uint8_t uu____0[1632U];
  memcpy(uu____0, value, (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey____1632size_t lit;
  memcpy(lit.value, uu____0, (size_t)1632U * sizeof(uint8_t));
  return lit;
}

libcrux_ml_kem_types_MlKemCiphertext____768size_t
libcrux_ml_kem_types___core__convert__From__Array_u8__SIZE___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___2__from___768size_t(
    uint8_t value[768U]) {
  uint8_t uu____0[768U];
  memcpy(uu____0, value, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext____768size_t lit;
  memcpy(lit.value, uu____0, (size_t)768U * sizeof(uint8_t));
  return lit;
}

uint8_t *
libcrux_ml_kem_types__libcrux_ml_kem__types__MlKemPublicKey_SIZE__18__as_slice___800size_t(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *self) {
  return self->value;
}

void libcrux_ml_kem_utils_into_padded_array___33size_t(Eurydice_slice slice,
                                                       uint8_t ret[33U]) {
  uint8_t out[33U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)33U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)33U * sizeof(uint8_t));
}

void core_result__core__result__Result_T__E___unwrap__uint8_t_32size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_32size_t__core_array_TryFromSliceError self,
    uint8_t ret[32U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[32U];
    memcpy(f0, self.val.case_Ok, (size_t)32U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)32U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

void libcrux_ml_kem_utils_into_padded_array___34size_t(Eurydice_slice slice,
                                                       uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)34U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

Eurydice_slice
libcrux_ml_kem_types___core__convert__AsRef__Slice_u8___for_libcrux_ml_kem__types__MlKemCiphertext_SIZE___1__as_ref___768size_t(
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *self) {
  return Eurydice_array_to_slice((size_t)768U, self->value, uint8_t,
                                 Eurydice_slice);
}

void libcrux_ml_kem_utils_into_padded_array___800size_t(Eurydice_slice slice,
                                                        uint8_t ret[800U]) {
  uint8_t out[800U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)800U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)800U * sizeof(uint8_t));
}

void libcrux_ml_kem_utils_into_padded_array___64size_t(Eurydice_slice slice,
                                                       uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  core_slice___Slice_T___copy_from_slice(
      Eurydice_array_to_subslice(
          (size_t)64U, uu____0,
          (CLITERAL(core_ops_range_Range__size_t){
              .start = (size_t)0U,
              .end = core_slice___Slice_T___len(slice, uint8_t, size_t)}),
          uint8_t, core_ops_range_Range__size_t, Eurydice_slice),
      slice, uint8_t, void *);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

void core_result__core__result__Result_T__E___unwrap__uint8_t_24size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_24size_t__core_array_TryFromSliceError self,
    uint8_t ret[24U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[24U];
    memcpy(f0, self.val.case_Ok, (size_t)24U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)24U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

void core_result__core__result__Result_T__E___unwrap__uint8_t_20size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_20size_t__core_array_TryFromSliceError self,
    uint8_t ret[20U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[20U];
    memcpy(f0, self.val.case_Ok, (size_t)20U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)20U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

void core_result__core__result__Result_T__E___unwrap__uint8_t_10size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_10size_t__core_array_TryFromSliceError self,
    uint8_t ret[10U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[10U];
    memcpy(f0, self.val.case_Ok, (size_t)10U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)10U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

void core_result__core__result__Result_T__E___unwrap__int16_t_16size_t__core_array_TryFromSliceError(
    core_result_Result__int16_t_16size_t__core_array_TryFromSliceError self,
    int16_t ret[16U]) {
  if (self.tag == core_result_Ok) {
    int16_t f0[16U];
    memcpy(f0, self.val.case_Ok, (size_t)16U * sizeof(int16_t));
    memcpy(ret, f0, (size_t)16U * sizeof(int16_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

void core_result__core__result__Result_T__E___unwrap__uint8_t_8size_t__core_array_TryFromSliceError(
    core_result_Result__uint8_t_8size_t__core_array_TryFromSliceError self,
    uint8_t ret[8U]) {
  if (self.tag == core_result_Ok) {
    uint8_t f0[8U];
    memcpy(f0, self.val.case_Ok, (size_t)8U * sizeof(uint8_t));
    memcpy(ret, f0, (size_t)8U * sizeof(uint8_t));
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}
