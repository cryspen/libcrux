/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: ac1a7e957d0dbcab6ae1a948e08b7a16b557851d
 * Karamel: 354791911c6b40d15a41cda7a0e3560da1cf31a1
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: d21c4cc2a58bda0db52962f7b838e8bde470f16b
 */

#include "internal/libcrux_mlkem_portable.h"

#include "internal/libcrux_core.h"
#include "libcrux_core.h"
#include "libcrux_sha3_portable.h"

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_G(
    Eurydice_slice input, uint8_t ret[64U]) {
  uint8_t digest[64U] = {0U};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)64U * sizeof(uint8_t));
}

KRML_MUSTINLINE void libcrux_ml_kem_hash_functions_portable_H(
    Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

static const int16_t ZETAS_TIMES_MONTGOMERY_R[128U] = {
    (int16_t)-1044, (int16_t)-758,  (int16_t)-359,  (int16_t)-1517,
    (int16_t)1493,  (int16_t)1422,  (int16_t)287,   (int16_t)202,
    (int16_t)-171,  (int16_t)622,   (int16_t)1577,  (int16_t)182,
    (int16_t)962,   (int16_t)-1202, (int16_t)-1474, (int16_t)1468,
    (int16_t)573,   (int16_t)-1325, (int16_t)264,   (int16_t)383,
    (int16_t)-829,  (int16_t)1458,  (int16_t)-1602, (int16_t)-130,
    (int16_t)-681,  (int16_t)1017,  (int16_t)732,   (int16_t)608,
    (int16_t)-1542, (int16_t)411,   (int16_t)-205,  (int16_t)-1571,
    (int16_t)1223,  (int16_t)652,   (int16_t)-552,  (int16_t)1015,
    (int16_t)-1293, (int16_t)1491,  (int16_t)-282,  (int16_t)-1544,
    (int16_t)516,   (int16_t)-8,    (int16_t)-320,  (int16_t)-666,
    (int16_t)-1618, (int16_t)-1162, (int16_t)126,   (int16_t)1469,
    (int16_t)-853,  (int16_t)-90,   (int16_t)-271,  (int16_t)830,
    (int16_t)107,   (int16_t)-1421, (int16_t)-247,  (int16_t)-951,
    (int16_t)-398,  (int16_t)961,   (int16_t)-1508, (int16_t)-725,
    (int16_t)448,   (int16_t)-1065, (int16_t)677,   (int16_t)-1275,
    (int16_t)-1103, (int16_t)430,   (int16_t)555,   (int16_t)843,
    (int16_t)-1251, (int16_t)871,   (int16_t)1550,  (int16_t)105,
    (int16_t)422,   (int16_t)587,   (int16_t)177,   (int16_t)-235,
    (int16_t)-291,  (int16_t)-460,  (int16_t)1574,  (int16_t)1653,
    (int16_t)-246,  (int16_t)778,   (int16_t)1159,  (int16_t)-147,
    (int16_t)-777,  (int16_t)1483,  (int16_t)-602,  (int16_t)1119,
    (int16_t)-1590, (int16_t)644,   (int16_t)-872,  (int16_t)349,
    (int16_t)418,   (int16_t)329,   (int16_t)-156,  (int16_t)-75,
    (int16_t)817,   (int16_t)1097,  (int16_t)603,   (int16_t)610,
    (int16_t)1322,  (int16_t)-1285, (int16_t)-1465, (int16_t)384,
    (int16_t)-1215, (int16_t)-136,  (int16_t)1218,  (int16_t)-1335,
    (int16_t)-874,  (int16_t)220,   (int16_t)-1187, (int16_t)-1659,
    (int16_t)-1185, (int16_t)-1530, (int16_t)-1278, (int16_t)794,
    (int16_t)-1510, (int16_t)-854,  (int16_t)-870,  (int16_t)478,
    (int16_t)-108,  (int16_t)-308,  (int16_t)996,   (int16_t)991,
    (int16_t)958,   (int16_t)-1460, (int16_t)1522,  (int16_t)1628};

int16_t libcrux_ml_kem_polynomial_zeta(size_t i) {
  return ZETAS_TIMES_MONTGOMERY_R[i];
}

KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_slice bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) &
      15U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
      15U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
      15U);
  int16_t v5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          4U &
      15U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) &
      15U);
  int16_t v7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          4U &
      15U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_4(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)4U, uint8_t *));
  int16_t_x8 v8_15 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)8U, uint8_t *));
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5,
                       v0_7.f6, v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd,
                       v8_15.f3, v8_15.f4, v8_15.f5, v8_15.f6, v8_15.f7}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_4(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_4(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_4_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_4(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_vector_type_to_i16_array(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    int16_t ret[16U]) {
  memcpy(ret, x.elements, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_to_i16_array_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    int16_t ret[16U]) {
  int16_t ret0[16U];
  libcrux_ml_kem_vector_portable_vector_type_to_i16_array(x, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_46(ret0, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  int16_t ret[16U];
  core_result_Result_0a dst;
  Eurydice_slice_to_array2(
      &dst, Eurydice_slice_subslice3(array, (size_t)0U, (size_t)16U, int16_t *),
      Eurydice_slice, int16_t[16U], core_array_TryFromSliceError);
  core_result_unwrap_26_00(dst, ret);
  memcpy(lit.elements, ret, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_from_i16_array_b8(Eurydice_slice array) {
  return libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
      libcrux_secrets_int_public_integers_classify_ref_c5_03(&array)[0U]);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_ml_kem_vector_portable_serialize_serialize_5_int(Eurydice_slice v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) |
      Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) << 5U);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      (Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 3U |
       Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) << 2U) |
      Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) << 7U);
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 1U |
      Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) << 4U);
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(
      (Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) >> 4U |
       Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *) << 1U) |
      Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) << 6U);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) >> 2U |
      Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *) << 3U);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = r0, .snd = r1, .thd = r2, .f3 = r3, .f4 = r4});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_5(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[10U]) {
  uint8_t_x5 r0_4 = libcrux_ml_kem_vector_portable_serialize_serialize_5_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)0U, (size_t)8U,
                                  int16_t *));
  uint8_t_x5 r5_9 = libcrux_ml_kem_vector_portable_serialize_serialize_5_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)8U, (size_t)16U,
                                  int16_t *));
  ret[0U] = r0_4.fst;
  ret[1U] = r0_4.snd;
  ret[2U] = r0_4.thd;
  ret[3U] = r0_4.f3;
  ret[4U] = r0_4.f4;
  ret[5U] = r5_9.fst;
  ret[6U] = r5_9.snd;
  ret[7U] = r5_9.thd;
  ret[8U] = r5_9.f3;
  ret[9U] = r5_9.f4;
}

void libcrux_ml_kem_vector_portable_serialize_5(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[10U]) {
  uint8_t ret0[10U];
  libcrux_ml_kem_vector_portable_serialize_serialize_5(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_cc(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_5_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[10U]) {
  libcrux_ml_kem_vector_portable_serialize_5(a, ret);
}

KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_slice bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) &
      31U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) &
       3U) << 3U |
      (uint32_t)Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *) >>
          5U);
  int16_t v2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          2U &
      31U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) &
       15U)
          << 1U |
      (uint32_t)Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *) >>
          7U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) &
       1U) << 4U |
      (uint32_t)Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *) >>
          4U);
  int16_t v5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          1U &
      31U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *) &
       7U) << 2U |
      (uint32_t)Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *) >>
          6U);
  int16_t v7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *) >>
      3U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_5(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)5U, uint8_t *));
  int16_t_x8 v8_15 = libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
      Eurydice_slice_subslice3(bytes, (size_t)5U, (size_t)10U, uint8_t *));
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5,
                       v0_7.f6, v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd,
                       v8_15.f3, v8_15.f4, v8_15.f5, v8_15.f6, v8_15.f7}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_5(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_5(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_5_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_5(a);
}

KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_slice bytes) {
  int16_t r0 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *)) &
       (int16_t)255));
  int16_t r1 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *)) >>
          2U);
  int16_t r2 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *)) >>
          4U);
  int16_t r3 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)4U, uint8_t, uint8_t *))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *)) >>
          6U);
  int16_t r4 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *)) &
       (int16_t)3)
          << 8U |
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)5U, uint8_t, uint8_t *)) &
       (int16_t)255));
  int16_t r5 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)) &
       (int16_t)15)
          << 6U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)6U, uint8_t, uint8_t *)) >>
          2U);
  int16_t r6 = libcrux_secrets_int_as_i16_f5(
      (libcrux_secrets_int_as_i16_59(
           Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *)) &
       (int16_t)63)
          << 4U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *)) >>
          4U);
  int16_t r7 = libcrux_secrets_int_as_i16_f5(
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)9U, uint8_t, uint8_t *))
          << 2U |
      libcrux_secrets_int_as_i16_59(
          Eurydice_slice_index(bytes, (size_t)8U, uint8_t, uint8_t *)) >>
          6U);
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_10(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)10U, uint8_t *));
  int16_t_x8 v8_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)10U, (size_t)20U, uint8_t *));
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5,
                       v0_7.f6, v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd,
                       v8_15.f3, v8_15.f4, v8_15.f5, v8_15.f6, v8_15.f7}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_10(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_10(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_10_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_10(a);
}

KRML_MUSTINLINE uint8_t_x11
libcrux_ml_kem_vector_portable_serialize_serialize_11_int(Eurydice_slice v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *));
  uint8_t r1 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) & (int16_t)31)
          << 3U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U);
  uint8_t r2 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) & (int16_t)3)
          << 6U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 5U);
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) >> 2U &
      (int16_t)255);
  uint8_t r4 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) &
          (int16_t)127)
          << 1U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) >> 10U);
  uint8_t r5 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) & (int16_t)15)
          << 4U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 7U);
  uint8_t r6 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *) & (int16_t)1)
          << 7U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)4U, int16_t, int16_t *) >> 4U);
  uint8_t r7 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *) >> 1U &
      (int16_t)255);
  uint8_t r8 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) & (int16_t)63)
          << 2U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *) >> 9U);
  uint8_t r9 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *) & (int16_t)7)
          << 5U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)6U, int16_t, int16_t *) >> 6U);
  uint8_t r10 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *) >> 3U);
  return (KRML_CLITERAL(uint8_t_x11){.fst = r0,
                                     .snd = r1,
                                     .thd = r2,
                                     .f3 = r3,
                                     .f4 = r4,
                                     .f5 = r5,
                                     .f6 = r6,
                                     .f7 = r7,
                                     .f8 = r8,
                                     .f9 = r9,
                                     .f10 = r10});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_11(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[22U]) {
  uint8_t_x11 r0_10 = libcrux_ml_kem_vector_portable_serialize_serialize_11_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)0U, (size_t)8U,
                                  int16_t *));
  uint8_t_x11 r11_21 =
      libcrux_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice3(v.elements, (size_t)8U, (size_t)16U,
                                      int16_t *));
  ret[0U] = r0_10.fst;
  ret[1U] = r0_10.snd;
  ret[2U] = r0_10.thd;
  ret[3U] = r0_10.f3;
  ret[4U] = r0_10.f4;
  ret[5U] = r0_10.f5;
  ret[6U] = r0_10.f6;
  ret[7U] = r0_10.f7;
  ret[8U] = r0_10.f8;
  ret[9U] = r0_10.f9;
  ret[10U] = r0_10.f10;
  ret[11U] = r11_21.fst;
  ret[12U] = r11_21.snd;
  ret[13U] = r11_21.thd;
  ret[14U] = r11_21.f3;
  ret[15U] = r11_21.f4;
  ret[16U] = r11_21.f5;
  ret[17U] = r11_21.f6;
  ret[18U] = r11_21.f7;
  ret[19U] = r11_21.f8;
  ret[20U] = r11_21.f9;
  ret[21U] = r11_21.f10;
}

void libcrux_ml_kem_vector_portable_serialize_11(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[22U]) {
  uint8_t ret0[22U];
  libcrux_ml_kem_vector_portable_serialize_serialize_11(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_fa(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_11_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[22U]) {
  libcrux_ml_kem_vector_portable_serialize_11(a, ret);
}

KRML_MUSTINLINE int16_t_x8
libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_slice bytes) {
  int16_t r0 = (libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                    bytes, (size_t)1U, uint8_t, uint8_t *)) &
                (int16_t)7)
                   << 8U |
               libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  int16_t r1 = (libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                    bytes, (size_t)2U, uint8_t, uint8_t *)) &
                (int16_t)63)
                   << 5U |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)1U, uint8_t, uint8_t *)) >>
                   3U;
  int16_t r2 = ((libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                     bytes, (size_t)4U, uint8_t, uint8_t *)) &
                 (int16_t)1)
                    << 10U |
                libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index(bytes, (size_t)3U, uint8_t, uint8_t *))
                    << 2U) |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)2U, uint8_t, uint8_t *)) >>
                   6U;
  int16_t r3 = (libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                    bytes, (size_t)5U, uint8_t, uint8_t *)) &
                (int16_t)15)
                   << 7U |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)4U, uint8_t, uint8_t *)) >>
                   1U;
  int16_t r4 = (libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                    bytes, (size_t)6U, uint8_t, uint8_t *)) &
                (int16_t)127)
                   << 4U |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)5U, uint8_t, uint8_t *)) >>
                   4U;
  int16_t r5 = ((libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                     bytes, (size_t)8U, uint8_t, uint8_t *)) &
                 (int16_t)3)
                    << 9U |
                libcrux_secrets_int_as_i16_59(
                    Eurydice_slice_index(bytes, (size_t)7U, uint8_t, uint8_t *))
                    << 1U) |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)6U, uint8_t, uint8_t *)) >>
                   7U;
  int16_t r6 = (libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                    bytes, (size_t)9U, uint8_t, uint8_t *)) &
                (int16_t)31)
                   << 6U |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)8U, uint8_t, uint8_t *)) >>
                   2U;
  int16_t r7 = libcrux_secrets_int_as_i16_59(
                   Eurydice_slice_index(bytes, (size_t)10U, uint8_t, uint8_t *))
                   << 3U |
               libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
                   bytes, (size_t)9U, uint8_t, uint8_t *)) >>
                   5U;
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_11(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)11U, uint8_t *));
  int16_t_x8 v8_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice3(bytes, (size_t)11U, (size_t)22U, uint8_t *));
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5,
                       v0_7.f6, v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd,
                       v8_15.f3, v8_15.f4, v8_15.f5, v8_15.f6, v8_15.f7}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_11(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_11(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_11_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_11(a);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_zero(void) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  int16_t ret[16U];
  int16_t buf[16U] = {0U};
  libcrux_secrets_int_public_integers_classify_27_46(buf, ret);
  memcpy(lit.elements, ret, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ZERO_b8(void) {
  return libcrux_ml_kem_vector_portable_vector_type_zero();
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_from_bytes(Eurydice_slice array) {
  int16_t elements[16U];
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U,
                   elements[i] = libcrux_secrets_int_I16((int16_t)0););
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    elements[i0] =
        libcrux_secrets_int_as_i16_59(
            Eurydice_slice_index(array, (size_t)2U * i0, uint8_t, uint8_t *))
            << 8U |
        libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
            array, (size_t)2U * i0 + (size_t)1U, uint8_t, uint8_t *));
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_elements[16U];
  memcpy(copy_of_elements, elements, (size_t)16U * sizeof(int16_t));
  libcrux_ml_kem_vector_portable_vector_type_PortableVector lit;
  memcpy(lit.elements, copy_of_elements, (size_t)16U * sizeof(int16_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_from_bytes_b8(Eurydice_slice array) {
  return libcrux_ml_kem_vector_portable_vector_type_from_bytes(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&array)[0U]);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_vector_type_to_bytes(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    Eurydice_slice_index(bytes, (size_t)2U * i0, uint8_t, uint8_t *) =
        libcrux_secrets_int_as_u8_f5(x.elements[i0] >> 8U);
    Eurydice_slice_index(bytes, (size_t)2U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) =
        libcrux_secrets_int_as_u8_f5(x.elements[i0]);
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_to_bytes_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector x,
    Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_to_bytes(
      x, libcrux_secrets_int_public_integers_classify_mut_slice_ba(bytes));
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_add(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.elements[uu____0] = lhs.elements[uu____0] + rhs->elements[i0];
  }
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_add_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_sub(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.elements[uu____0] = lhs.elements[uu____0] - rhs->elements[i0];
  }
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_sub_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.elements[uu____0] = vec.elements[uu____0] * c;
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_multiply_by_constant_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  return libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (libcrux_secrets_int_public_integers_declassify_d8_39(
            vec.elements[i0]) >= (int16_t)3329) {
      size_t uu____0 = i0;
      vec.elements[uu____0] = vec.elements[uu____0] - (int16_t)3329;
    }
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v) {
  return libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(v);
}

/**
 Signed Barrett Reduction

 Given an input `value`, `barrett_reduce` outputs a representative `result`
 such that:

 - result ≡ value (mod FIELD_MODULUS)
 - the absolute value of `result` is bound as follows:

 `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)

 Note: The input bound is 28296 to prevent overflow in the multiplication of
 quotient by FIELD_MODULUS

*/
int16_t libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value) {
  int32_t t = libcrux_secrets_int_as_i32_f5(value) *
                  LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER +
              (LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient = libcrux_secrets_int_as_i16_36(
      t >> (uint32_t)LIBCRUX_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  return value - quotient * LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec.elements[i0]);
    vec.elements[i0] = vi;
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_barrett_reduce_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vector) {
  return libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(vector);
}

/**
 Signed Montgomery Reduction

 Given an input `value`, `montgomery_reduce` outputs a representative `o`
 such that:

 - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
 - the absolute value of `o` is bound as follows:

 `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665

 In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS-1`. And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS + 1664

*/
int16_t libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
    int32_t value) {
  int32_t k =
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(value)) *
      libcrux_secrets_int_as_i32_b8(
          libcrux_secrets_int_public_integers_classify_27_df(
              LIBCRUX_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R));
  int32_t k_times_modulus =
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(k)) *
      libcrux_secrets_int_as_i32_f5(
          libcrux_secrets_int_public_integers_classify_27_39(
              LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  int16_t c = libcrux_secrets_int_as_i16_36(
      k_times_modulus >>
      (uint32_t)LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high = libcrux_secrets_int_as_i16_36(
      value >>
      (uint32_t)LIBCRUX_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
KRML_MUSTINLINE int16_t
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer) {
  int32_t product =
      libcrux_secrets_int_as_i32_f5(fe) * libcrux_secrets_int_as_i32_f5(fer);
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.elements[i0] =
        libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec.elements[i0], c);
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vector,
    int16_t constant) {
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vector, libcrux_secrets_int_public_integers_classify_27_39(constant));
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.elements[uu____0] = vec.elements[uu____0] & c;
  }
  return vec;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
shift_right_ef(libcrux_ml_kem_vector_portable_vector_type_PortableVector vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.elements[i0] = vec.elements[i0] >> (uint32_t)(int32_t)15;
  }
  return vec;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
      shift_right_ef(a);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector fm =
      libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_portable_arithmetic_add(a, &fm);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(
      a);
}

/**
 The `compress_*` functions implement the `Compress` function specified in the
 NIST FIPS 203 standard (Page 18, Expression 4.5), which is defined as:

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
uint8_t libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe) {
  int16_t shifted =
      libcrux_secrets_int_public_integers_classify_27_39((int16_t)1664) -
      libcrux_secrets_int_as_i16_ca(fe);
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range = shifted_to_positive - (int16_t)832;
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & (int16_t)1;
  return libcrux_secrets_int_as_u8_f5(r1);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_compress_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    a.elements[i0] = libcrux_secrets_int_as_i16_59(
        libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
            libcrux_secrets_int_as_u16_f5(a.elements[i0])));
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_1_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_compress_1(a);
}

KRML_MUSTINLINE uint32_t
libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  return value & ((1U << (uint32_t)n) - 1U);
}

int16_t libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = libcrux_secrets_int_as_u64_ca(fe)
                        << (uint32_t)coefficient_bits;
  compressed = compressed + 1664ULL;
  compressed = compressed * 10321340ULL;
  compressed = compressed >> 35U;
  return libcrux_secrets_int_as_i16_b8(
      libcrux_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, libcrux_secrets_int_as_u32_a3(compressed)));
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_compress_decompress_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector z =
      libcrux_ml_kem_vector_portable_vector_type_zero();
  libcrux_ml_kem_vector_portable_vector_type_PortableVector s =
      libcrux_ml_kem_vector_portable_arithmetic_sub(z, &a);
  libcrux_ml_kem_vector_portable_vector_type_PortableVector res =
      libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
          s, (int16_t)1665);
  return res;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_decompress_1_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_compress_decompress_1(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->elements[j],
          libcrux_secrets_int_public_integers_classify_27_39(zeta));
  int16_t a_minus_t = vec->elements[i] - t;
  int16_t a_plus_t = vec->elements[i] + t;
  vec->elements[j] = a_minus_t;
  vec->elements[i] = a_plus_t;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)0U,
                                              (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)1U,
                                              (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)4U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)5U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta2, (size_t)8U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta2, (size_t)9U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta3, (size_t)12U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta3, (size_t)13U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                             zeta2, zeta3);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)0U,
                                              (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)1U,
                                              (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)2U,
                                              (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta0, (size_t)3U,
                                              (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)8U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)9U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)10U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta1, (size_t)11U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)0U,
                                              (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)1U,
                                              (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)2U,
                                              (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)3U,
                                              (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)4U,
                                              (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)5U,
                                              (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)6U,
                                              (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_ntt_step(&vec, zeta, (size_t)7U,
                                              (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *vec,
    int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = vec->elements[j] - vec->elements[i];
  int16_t a_plus_b = vec->elements[j] + vec->elements[i];
  int16_t o0 = libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
      a_plus_b);
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_39(zeta));
  vec->elements[i] = o0;
  vec->elements[j] = o1;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)0U,
                                                  (size_t)2U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)1U,
                                                  (size_t)3U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)4U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)5U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta2, (size_t)8U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta2, (size_t)9U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta3, (size_t)12U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta3, (size_t)13U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
      a, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta0, int16_t zeta1) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)0U,
                                                  (size_t)4U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)1U,
                                                  (size_t)5U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)2U,
                                                  (size_t)6U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta0, (size_t)3U,
                                                  (size_t)7U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)8U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)9U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)10U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta1, (size_t)11U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta0,
    int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0,
                                                                 zeta1);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vec,
    int16_t zeta) {
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)0U,
                                                  (size_t)8U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)1U,
                                                  (size_t)9U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)2U,
                                                  (size_t)10U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)3U,
                                                  (size_t)11U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)4U,
                                                  (size_t)12U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)5U,
                                                  (size_t)13U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)6U,
                                                  (size_t)14U);
  libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(&vec, zeta, (size_t)7U,
                                                  (size_t)15U);
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a, int16_t zeta) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
}

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
KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *a,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *b, int16_t zeta,
    size_t i, libcrux_ml_kem_vector_portable_vector_type_PortableVector *out) {
  int16_t ai = a->elements[(size_t)2U * i];
  int16_t bi = b->elements[(size_t)2U * i];
  int16_t aj = a->elements[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->elements[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi =
      libcrux_secrets_int_as_i32_f5(ai) * libcrux_secrets_int_as_i32_f5(bi);
  int32_t aj_bj_ =
      libcrux_secrets_int_as_i32_f5(aj) * libcrux_secrets_int_as_i32_f5(bj);
  int16_t aj_bj =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          aj_bj_);
  int32_t aj_bj_zeta = libcrux_secrets_int_as_i32_f5(aj_bj) *
                       libcrux_secrets_int_as_i32_f5(zeta);
  int32_t ai_bi_aj_bj = ai_bi + aj_bj_zeta;
  int16_t o0 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bi_aj_bj);
  int32_t ai_bj =
      libcrux_secrets_int_as_i32_f5(ai) * libcrux_secrets_int_as_i32_f5(bj);
  int32_t aj_bi =
      libcrux_secrets_int_as_i32_f5(aj) * libcrux_secrets_int_as_i32_f5(bi);
  int32_t ai_bj_aj_bi = ai_bj + aj_bi;
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          ai_bj_aj_bi);
  out->elements[(size_t)2U * i] = o0;
  out->elements[(size_t)2U * i + (size_t)1U] = o1;
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector out =
      libcrux_ml_kem_vector_portable_vector_type_zero();
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, &out);
  libcrux_ml_kem_vector_portable_ntt_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, &out);
  return out;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_ntt_multiply_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *lhs,
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *rhs,
    int16_t zeta0, int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_multiply(lhs, rhs, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[2U]) {
  uint8_t result0 =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[0U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[1U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[2U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[3U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[4U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[5U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[6U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[7U]) << 7U;
  uint8_t result1 =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[8U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[9U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[10U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[11U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[12U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[13U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[14U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v.elements[15U]) << 7U;
  ret[0U] = result0;
  ret[1U] = result1;
}

void libcrux_ml_kem_vector_portable_serialize_1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[2U]) {
  uint8_t ret0[2U];
  libcrux_ml_kem_vector_portable_serialize_serialize_1(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_d4(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_1_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[2U]) {
  libcrux_ml_kem_vector_portable_serialize_1(a, ret);
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_1(Eurydice_slice v) {
  int16_t result0 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) & 1U);
  int16_t result1 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 1U &
      1U);
  int16_t result2 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 2U &
      1U);
  int16_t result3 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 3U &
      1U);
  int16_t result4 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 4U &
      1U);
  int16_t result5 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 5U &
      1U);
  int16_t result6 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 6U &
      1U);
  int16_t result7 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)0U, uint8_t, uint8_t *) >> 7U &
      1U);
  int16_t result8 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) & 1U);
  int16_t result9 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 1U &
      1U);
  int16_t result10 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 2U &
      1U);
  int16_t result11 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 3U &
      1U);
  int16_t result12 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 4U &
      1U);
  int16_t result13 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 5U &
      1U);
  int16_t result14 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 6U &
      1U);
  int16_t result15 = libcrux_secrets_int_as_i16_59(
      (uint32_t)Eurydice_slice_index(v, (size_t)1U, uint8_t, uint8_t *) >> 7U &
      1U);
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {result0, result1, result2, result3, result4, result5,
                       result6, result7, result8, result9, result10, result11,
                       result12, result13, result14, result15}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_1(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_1(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_1_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_1(a);
}

KRML_MUSTINLINE uint8_t_x4
libcrux_ml_kem_vector_portable_serialize_serialize_4_int(Eurydice_slice v) {
  uint8_t result0 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)0U, int16_t, int16_t *));
  uint8_t result1 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)2U, int16_t, int16_t *));
  uint8_t result2 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)5U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)4U, int16_t, int16_t *));
  uint8_t result3 = (uint32_t)libcrux_secrets_int_as_u8_f5(
                        Eurydice_slice_index(v, (size_t)7U, int16_t, int16_t *))
                        << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(Eurydice_slice_index(
                        v, (size_t)6U, int16_t, int16_t *));
  return (KRML_CLITERAL(uint8_t_x4){
      .fst = result0, .snd = result1, .thd = result2, .f3 = result3});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[8U]) {
  uint8_t_x4 result0_3 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(v.elements, (size_t)0U, (size_t)8U,
                                      int16_t *));
  uint8_t_x4 result4_7 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(v.elements, (size_t)8U, (size_t)16U,
                                      int16_t *));
  ret[0U] = result0_3.fst;
  ret[1U] = result0_3.snd;
  ret[2U] = result0_3.thd;
  ret[3U] = result0_3.f3;
  ret[4U] = result4_7.fst;
  ret[5U] = result4_7.snd;
  ret[6U] = result4_7.thd;
  ret[7U] = result4_7.f3;
}

void libcrux_ml_kem_vector_portable_serialize_4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[8U]) {
  uint8_t ret0[8U];
  libcrux_ml_kem_vector_portable_serialize_serialize_4(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_76(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_4_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[8U]) {
  libcrux_ml_kem_vector_portable_serialize_4(a, ret);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_ml_kem_vector_portable_serialize_serialize_10_int(Eurydice_slice v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) & (int16_t)255);
  uint8_t r1 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) & (int16_t)63)
          << 2U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U &
          (int16_t)3);
  uint8_t r2 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) & (int16_t)15)
          << 4U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 6U &
          (int16_t)15);
  uint8_t r3 =
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) & (int16_t)3)
          << 6U |
      (uint32_t)libcrux_secrets_int_as_u8_f5(
          Eurydice_slice_index(v, (size_t)2U, int16_t, int16_t *) >> 4U &
          (int16_t)63);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)3U, int16_t, int16_t *) >> 2U &
      (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = r0, .snd = r1, .thd = r2, .f3 = r3, .f4 = r4});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[20U]) {
  uint8_t_x5 r0_4 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)0U, (size_t)4U,
                                  int16_t *));
  uint8_t_x5 r5_9 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)4U, (size_t)8U,
                                  int16_t *));
  uint8_t_x5 r10_14 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)8U, (size_t)12U,
                                  int16_t *));
  uint8_t_x5 r15_19 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)12U, (size_t)16U,
                                  int16_t *));
  ret[0U] = r0_4.fst;
  ret[1U] = r0_4.snd;
  ret[2U] = r0_4.thd;
  ret[3U] = r0_4.f3;
  ret[4U] = r0_4.f4;
  ret[5U] = r5_9.fst;
  ret[6U] = r5_9.snd;
  ret[7U] = r5_9.thd;
  ret[8U] = r5_9.f3;
  ret[9U] = r5_9.f4;
  ret[10U] = r10_14.fst;
  ret[11U] = r10_14.snd;
  ret[12U] = r10_14.thd;
  ret[13U] = r10_14.f3;
  ret[14U] = r10_14.f4;
  ret[15U] = r15_19.fst;
  ret[16U] = r15_19.snd;
  ret[17U] = r15_19.thd;
  ret[18U] = r15_19.f3;
  ret[19U] = r15_19.f4;
}

void libcrux_ml_kem_vector_portable_serialize_10(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[20U]) {
  uint8_t ret0[20U];
  libcrux_ml_kem_vector_portable_serialize_serialize_10(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_57(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_10_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[20U]) {
  libcrux_ml_kem_vector_portable_serialize_10(a, ret);
}

KRML_MUSTINLINE uint8_t_x3
libcrux_ml_kem_vector_portable_serialize_serialize_12_int(Eurydice_slice v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) & (int16_t)255);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)0U, int16_t, int16_t *) >> 8U |
      (Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) & (int16_t)15)
          << 4U);
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      Eurydice_slice_index(v, (size_t)1U, int16_t, int16_t *) >> 4U &
      (int16_t)255);
  return (KRML_CLITERAL(uint8_t_x3){.fst = r0, .snd = r1, .thd = r2});
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_serialize_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector v,
    uint8_t ret[24U]) {
  uint8_t_x3 r0_2 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)0U, (size_t)2U,
                                  int16_t *));
  uint8_t_x3 r3_5 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)2U, (size_t)4U,
                                  int16_t *));
  uint8_t_x3 r6_8 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)4U, (size_t)6U,
                                  int16_t *));
  uint8_t_x3 r9_11 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)6U, (size_t)8U,
                                  int16_t *));
  uint8_t_x3 r12_14 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)8U, (size_t)10U,
                                  int16_t *));
  uint8_t_x3 r15_17 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)10U, (size_t)12U,
                                  int16_t *));
  uint8_t_x3 r18_20 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)12U, (size_t)14U,
                                  int16_t *));
  uint8_t_x3 r21_23 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(v.elements, (size_t)14U, (size_t)16U,
                                  int16_t *));
  ret[0U] = r0_2.fst;
  ret[1U] = r0_2.snd;
  ret[2U] = r0_2.thd;
  ret[3U] = r3_5.fst;
  ret[4U] = r3_5.snd;
  ret[5U] = r3_5.thd;
  ret[6U] = r6_8.fst;
  ret[7U] = r6_8.snd;
  ret[8U] = r6_8.thd;
  ret[9U] = r9_11.fst;
  ret[10U] = r9_11.snd;
  ret[11U] = r9_11.thd;
  ret[12U] = r12_14.fst;
  ret[13U] = r12_14.snd;
  ret[14U] = r12_14.thd;
  ret[15U] = r15_17.fst;
  ret[16U] = r15_17.snd;
  ret[17U] = r15_17.thd;
  ret[18U] = r18_20.fst;
  ret[19U] = r18_20.snd;
  ret[20U] = r18_20.thd;
  ret[21U] = r21_23.fst;
  ret[22U] = r21_23.snd;
  ret[23U] = r21_23.thd;
}

void libcrux_ml_kem_vector_portable_serialize_12(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[24U]) {
  uint8_t ret0[24U];
  libcrux_ml_kem_vector_portable_serialize_serialize_12(a, ret0);
  libcrux_secrets_int_public_integers_declassify_d8_d2(ret0, ret);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_serialize_12_b8(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
    uint8_t ret[24U]) {
  libcrux_ml_kem_vector_portable_serialize_12(a, ret);
}

KRML_MUSTINLINE int16_t_x2
libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_slice bytes) {
  int16_t byte0 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)0U, uint8_t, uint8_t *));
  int16_t byte1 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)1U, uint8_t, uint8_t *));
  int16_t byte2 = libcrux_secrets_int_as_i16_59(
      Eurydice_slice_index(bytes, (size_t)2U, uint8_t, uint8_t *));
  int16_t r0 = (byte1 & (int16_t)15) << 8U | (byte0 & (int16_t)255);
  int16_t r1 = byte2 << 4U | (byte1 >> 4U & (int16_t)15);
  return (KRML_CLITERAL(int16_t_x2){.fst = r0, .snd = r1});
}

KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_serialize_deserialize_12(Eurydice_slice bytes) {
  int16_t_x2 v0_1 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)3U, uint8_t *));
  int16_t_x2 v2_3 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice3(bytes, (size_t)3U, (size_t)6U, uint8_t *));
  int16_t_x2 v4_5 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice3(bytes, (size_t)6U, (size_t)9U, uint8_t *));
  int16_t_x2 v6_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice3(bytes, (size_t)9U, (size_t)12U, uint8_t *));
  int16_t_x2 v8_9 = libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
      Eurydice_slice_subslice3(bytes, (size_t)12U, (size_t)15U, uint8_t *));
  int16_t_x2 v10_11 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)15U, (size_t)18U, uint8_t *));
  int16_t_x2 v12_13 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)18U, (size_t)21U, uint8_t *));
  int16_t_x2 v14_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice3(bytes, (size_t)21U, (size_t)24U, uint8_t *));
  return (
      KRML_CLITERAL(libcrux_ml_kem_vector_portable_vector_type_PortableVector){
          .elements = {v0_1.fst, v0_1.snd, v2_3.fst, v2_3.snd, v4_5.fst,
                       v4_5.snd, v6_7.fst, v6_7.snd, v8_9.fst, v8_9.snd,
                       v10_11.fst, v10_11.snd, v12_13.fst, v12_13.snd,
                       v14_15.fst, v14_15.snd}});
}

libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_12(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_12(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_deserialize_12_b8(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_12(a);
}

KRML_MUSTINLINE size_t libcrux_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_slice a, Eurydice_slice result) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(a, uint8_t) / (size_t)3U;
       i++) {
    size_t i0 = i;
    int16_t b1 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)0U,
                                               uint8_t, uint8_t *);
    int16_t b2 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)1U,
                                               uint8_t, uint8_t *);
    int16_t b3 = (int16_t)Eurydice_slice_index(a, i0 * (size_t)3U + (size_t)2U,
                                               uint8_t, uint8_t *);
    int16_t d1 = (b2 & (int16_t)15) << 8U | b1;
    int16_t d2 = b3 << 4U | b2 >> 4U;
    if (d1 < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d1;
        sampled++;
      }
    }
    if (d2 < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        Eurydice_slice_index(result, sampled, int16_t, int16_t *) = d2;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
size_t libcrux_ml_kem_vector_portable_rej_sample_b8(Eurydice_slice a,
                                                    Eurydice_slice out) {
  return libcrux_ml_kem_vector_portable_sampling_rej_sample(a, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
inline libcrux_ml_kem_vector_portable_vector_type_PortableVector
libcrux_ml_kem_vector_portable_vector_type_clone_9c(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector *self) {
  return self[0U];
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d ZERO_d6_ea(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector
      repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_b8(););
  memcpy(lit.coefficients, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
 Only use with public values.

 This MUST NOT be used with secret inputs, like its caller
 `deserialize_ring_elements_reduced`.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_to_reduced_ring_element_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_d0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash_44
shake128_init_absorb_final_ac(uint8_t (*input)[34U]) {
  libcrux_ml_kem_hash_functions_portable_PortableHash_44 shake128_state;
  libcrux_sha3_generic_keccak_KeccakState_17 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.shake128_state, repeat_expression,
         (size_t)4U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.shake128_state[i0],
          Eurydice_array_to_slice((size_t)34U, input[i0], uint8_t)););
  return shake128_state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final_4a with const
generics
- K= 4
*/
libcrux_ml_kem_hash_functions_portable_PortableHash_44
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
    uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_ac(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_ac(
    libcrux_ml_kem_hash_functions_portable_PortableHash_44 *st,
    uint8_t ret[4U][504U]) {
  uint8_t out[4U][504U] = {{0U}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)504U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks_4a
with const generics
- K= 4
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
    libcrux_ml_kem_hash_functions_portable_PortableHash_44 *self,
    uint8_t ret[4U][504U]) {
  shake128_squeeze_first_three_blocks_ac(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_ff(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block with const
generics
- K= 4
*/
static KRML_MUSTINLINE void shake128_squeeze_next_block_ac(
    libcrux_ml_kem_hash_functions_portable_PortableHash_44 *st,
    uint8_t ret[4U][168U]) {
  uint8_t out[4U][168U] = {{0U}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)168U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block_4a with const
generics
- K= 4
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
    libcrux_ml_kem_hash_functions_portable_PortableHash_44 *self,
    uint8_t ret[4U][168U]) {
  shake128_squeeze_next_block_ac(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_ff0(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d ZERO_ea(void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector
      repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_b8(););
  memcpy(lit.coefficients, repeat_expression,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
from_i16_array_ea(Eurydice_slice a) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_ea();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_from_i16_array_b8(
            Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                     (i0 + (size_t)1U) * (size_t)16U,
                                     int16_t *));
    result.coefficients[i0] = uu____0;
  }
  return result;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
from_i16_array_d6_ea(Eurydice_slice a) {
  return from_i16_array_ea(a);
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_e7_2b1(
    int16_t tupled_args[272U]) {
  int16_t s[272U];
  memcpy(s, tupled_args, (size_t)272U * sizeof(int16_t));
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_2b1(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U]) {
  size_t sampled_coefficients[4U] = {0U};
  int16_t out[4U][272U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_PortableHash_44 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
          seeds);
  uint8_t randomness0[4U][504U];
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
      &xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_ff(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[4U][168U];
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
          &xof_state, randomness);
      done = sample_from_uniform_distribution_next_ff0(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[4U][272U];
  memcpy(copy_of_out, out, (size_t)4U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  ret0[i] = call_mut_e7_2b1(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_2b1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*A_transpose)[4U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[4U][34U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d sampled[4U];
      sample_from_xof_2b1(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)4U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1d sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.H_4a
with const generics
- K= 4
*/
static KRML_MUSTINLINE void H_4a_ac(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_portable_H(input, ret);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_30(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
        *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice_to((size_t)1568U, public_key->value,
                                    (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_d0(
      uu____0, unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key->value,
                                      (size_t)1536U, uint8_t, size_t,
                                      uint8_t[]),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____2)[4U] =
      unpacked_public_key->ind_cpa_public_key.A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key->value,
                                      (size_t)1536U, uint8_t, size_t,
                                      uint8_t[]),
      ret);
  sample_matrix_A_2b1(uu____2, ret, false);
  uint8_t uu____3[32U];
  H_4a_ac(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key),
              uint8_t),
          uu____3);
  memcpy(unpacked_public_key->public_key_hash, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
to_unsigned_field_modulus_ea(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[384U]) {
  uint8_t serialized[384U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        to_unsigned_field_modulus_ea(re->coefficients[i0]);
    uint8_t bytes[24U];
    libcrux_ml_kem_vector_portable_serialize_12_b8(coefficient, bytes);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(serialized, (size_t)24U * i0,
                                    (size_t)24U * i0 + (size_t)24U, uint8_t *),
        Eurydice_array_to_slice((size_t)24U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)384U * sizeof(uint8_t));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void serialize_vector_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_ea(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_ff(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  serialize_vector_d0(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1568U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_ff(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *self,
    libcrux_ml_kem_types_MlKemPublicKey_64 *serialized) {
  serialize_public_key_mut_ff(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_ff(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_64 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_ff(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_ff(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1568U]) {
  uint8_t public_key_serialized[1568U] = {0U};
  serialize_public_key_mut_ff(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1568U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_64 serialized_dd_ff(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *self) {
  uint8_t ret[1568U];
  serialize_public_key_ff(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      ret);
  return libcrux_ml_kem_types_from_fd_af(ret);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_64
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_ff(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *self) {
  return serialized_dd_ff(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair1024
serialize_unpacked_secret_key_00(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af *private_key) {
  uint8_t public_key_serialized[1568U];
  serialize_public_key_ff(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1536U] = {0U};
  serialize_vector_d0(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)1536U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1536U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1568U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1536U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1568U * sizeof(uint8_t));
  return lit;
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  uint8_t ret[32U];
  H_4a_ac(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2f(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_83 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      serialize_unpacked_secret_key_00(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t ind_cpa_public_key[1568U];
  memcpy(ind_cpa_public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPrivateKey_83
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_2f(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_83 sk =
      libcrux_ml_kem_types_default_d3_39();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2f(self, &sk);
  return sk;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_to_uncompressed_ring_element_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_vector_d0(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt[i0] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_3f1(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_d0(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[4U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_2b1(uu____1, ret, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_7d(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_d0(
      ind_cpa_secret_key,
      key_pair->private_key.ind_cpa_private_key.secret_as_ntt);
  build_unpacked_public_key_mut_3f1(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1536U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af
default_70_d0(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af default_8b_d0(
    void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  uu____0[i] = ZERO_d6_ea(););
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression0[4U][4U];
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[4U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)4U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d)););
  memcpy(lit.A, repeat_expression0,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
libcrux_ml_kem_ind_cca_unpacked_default_30_d0(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af){
          .ind_cpa_public_key = default_8b_d0(),
          .public_key_hash = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_d0(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_af uu____0 = {
      .ind_cpa_private_key = default_70_d0(), .implicit_rejection_value = {0U}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_d0()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.G_4a
with const generics
- K= 4
*/
static KRML_MUSTINLINE void G_4a_ac(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_portable_G(input, ret);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
*/
static KRML_MUSTINLINE void cpa_keygen_seed_39_03(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  uint8_t ret0[64U];
  G_4a_ac(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_44(uint8_t (*input)[33U],
                                     uint8_t ret[4U][128U]) {
  uint8_t out[4U][128U] = {{0U}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, out[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, input[i0], uint8_t)););
  memcpy(ret, out, (size_t)4U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN_4a
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_4a_44(uint8_t (*input)[33U],
                                        uint8_t ret[4U][128U]) {
  PRFxN_44(input, ret);
}

/**
 Given a series of uniformly random bytes in `randomness`, for some number
 `eta`, the `sample_from_binomial_distribution_{eta}` functions sample a ring
 element from a binomial distribution centered at 0 that uses two sets of `eta`
 coin flips. If, for example, `eta = ETA`, each ring coefficient is a value `v`
 such such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:

 ```plaintext
 - If v < 0, Pr[v] = Pr[-v]
 - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
 ```

 The values `v < 0` are mapped to the appropriate `KyberFieldElement`.

 The expected value is:

 ```plaintext
 E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1]
 + (ETA)Pr[ETA] = 0 since Pr[-v] = Pr[v] when v < 0.
 ```

 And the variance is:

 ```plaintext
 Var(X) = E[(X - E[X])^2]
        = E[X^2]
        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) /
 2^(2 * ETA)) = ETA / 2
 ```

 This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203
 standard, which is reproduced below:

 ```plaintext
 Input: byte array B ∈ 𝔹^{64η}.
 Output: array f ∈ ℤ₂₅₆.

 b ← BytesToBits(B)
 for (i ← 0; i < 256; i++)
     x ← ∑(j=0 to η - 1) b[2iη + j]
     y ← ∑(j=0 to η - 1) b[2iη + η + j]
     f[i] ← x−y mod q
 end for
 return f
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
sample_from_binomial_distribution_2_ea(Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)4U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)4U,
        chunk_number * (size_t)4U + (size_t)4U, uint8_t *);
    uint32_t random_bits_as_u32 =
        (((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                         uint8_t *) |
          (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                         uint8_t *)
              << 8U) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                        uint8_t *)
             << 16U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)3U, uint8_t,
                                       uint8_t *)
            << 24U;
    uint32_t even_bits = random_bits_as_u32 & 1431655765U;
    uint32_t odd_bits = random_bits_as_u32 >> 1U & 1431655765U;
    uint32_t coin_toss_outcomes = even_bits + odd_bits;
    for (uint32_t i = 0U; i < core_num__u32__BITS / 4U; i++) {
      uint32_t outcome_set = i;
      uint32_t outcome_set0 = outcome_set * 4U;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 3U);
      int16_t outcome_2 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)(outcome_set0 + 2U) & 3U);
      size_t offset = (size_t)(outcome_set0 >> 2U);
      sampled_i16s[(size_t)8U * chunk_number + offset] = outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_ea(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
sample_from_binomial_distribution_3_ea(Eurydice_slice randomness) {
  int16_t sampled_i16s[256U] = {0U};
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(randomness, uint8_t) / (size_t)3U; i0++) {
    size_t chunk_number = i0;
    Eurydice_slice byte_chunk = Eurydice_slice_subslice3(
        randomness, chunk_number * (size_t)3U,
        chunk_number * (size_t)3U + (size_t)3U, uint8_t *);
    uint32_t random_bits_as_u24 =
        ((uint32_t)Eurydice_slice_index(byte_chunk, (size_t)0U, uint8_t,
                                        uint8_t *) |
         (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)1U, uint8_t,
                                        uint8_t *)
             << 8U) |
        (uint32_t)Eurydice_slice_index(byte_chunk, (size_t)2U, uint8_t,
                                       uint8_t *)
            << 16U;
    uint32_t first_bits = random_bits_as_u24 & 2396745U;
    uint32_t second_bits = random_bits_as_u24 >> 1U & 2396745U;
    uint32_t third_bits = random_bits_as_u24 >> 2U & 2396745U;
    uint32_t coin_toss_outcomes = first_bits + second_bits + third_bits;
    for (int32_t i = (int32_t)0; i < (int32_t)24 / (int32_t)6; i++) {
      int32_t outcome_set = i;
      int32_t outcome_set0 = outcome_set * (int32_t)6;
      int16_t outcome_1 =
          (int16_t)(coin_toss_outcomes >> (uint32_t)outcome_set0 & 7U);
      int16_t outcome_2 = (int16_t)(coin_toss_outcomes >>
                                        (uint32_t)(outcome_set0 + (int32_t)3) &
                                    7U);
      size_t offset = (size_t)(outcome_set0 / (int32_t)6);
      sampled_i16s[(size_t)4U * chunk_number + offset] = outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_ea(
      Eurydice_array_to_slice((size_t)256U, sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
sample_from_binomial_distribution_a0(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_ea(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
        libcrux_ml_kem_vector_portable_multiply_by_constant_b8(
            re->coefficients[j + step], (int16_t)-1600);
    re->coefficients[j + step] =
        libcrux_ml_kem_vector_portable_sub_b8(re->coefficients[j], &t);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____1 =
        libcrux_ml_kem_vector_portable_add_b8(re->coefficients[j], &t);
    re->coefficients[j] = uu____1;
  }
}

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2_s {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector fst;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector snd;
} libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2;

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    ntt_layer_int_vec_step_ea(
        libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
        libcrux_ml_kem_vector_portable_vector_type_PortableVector b,
        int16_t zeta_r) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector t =
      libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(b,
                                                                        zeta_r);
  b = libcrux_ml_kem_vector_portable_sub_b8(a, &t);
  a = libcrux_ml_kem_vector_portable_add_b8(a, &t);
  return (KRML_CLITERAL(
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2){.fst = a,
                                                                    .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t layer) {
  size_t step = (size_t)1U << (uint32_t)layer;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] + (size_t)1U;
    size_t offset = round * step * (size_t)2U;
    size_t offset_vec = offset / (size_t)16U;
    size_t step_vec = step / (size_t)16U;
    for (size_t i = offset_vec; i < offset_vec + step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2 uu____0 =
          ntt_layer_int_vec_step_ea(re->coefficients[j],
                                    re->coefficients[j + step_vec],
                                    libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_portable_vector_type_PortableVector x = uu____0.fst;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
          libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->coefficients[round] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)2U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)3U));
      zeta_i[0U] = zeta_i[0U] + (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(
            myself->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.poly_barrett_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_d6_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  poly_barrett_reduce_ea(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  ntt_at_layer_7_ea(re);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ea(&zeta_i, re);
  ntt_at_layer_2_ea(&zeta_i, re);
  ntt_at_layer_1_ea(&zeta_i, re);
  poly_barrett_reduce_d6_ea(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_3b1(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[4U][128U];
  PRFxN_4a_44(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_73_1c1(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Given two `KyberPolynomialRingElement`s in their NTT representations,
 compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
 the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:

 ```plaintext
 ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X²
 - ζ^(2·BitRev₇(i) + 1))
 ```

 This function almost implements <strong>Algorithm 10</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
 Output: An array ĥ ∈ ℤq.

 for(i ← 0; i < 128; i++)
     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1],
 ζ^(2·BitRev₇(i) + 1)) end for return ĥ
 ```
 We say "almost" because the coefficients of the ring element output by
 this function are in the Montgomery domain.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
ntt_multiply_ea(libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
                libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d out = ZERO_ea();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_ntt_multiply_b8(
            &myself->coefficients[i0], &rhs->coefficients[i0],
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)1U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)2U),
            libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                           (size_t)3U));
    out.coefficients[i0] = uu____0;
  }
  return out;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.ntt_multiply_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
ntt_multiply_d6_ea(libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  return ntt_multiply_ea(self, rhs);
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself->coefficients,
                   libcrux_ml_kem_vector_portable_vector_type_PortableVector),
               libcrux_ml_kem_vector_portable_vector_type_PortableVector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->coefficients[i0],
                                              &rhs->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  add_to_ring_element_d0(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
to_standard_domain_ea(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector vector) {
  return libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
      vector,
      LIBCRUX_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            to_standard_domain_ea(myself->coefficients[j]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector sum =
        libcrux_ml_kem_vector_portable_add_b8(coefficient_normal_form,
                                              &error->coefficients[j]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum);
    myself->coefficients[j] = red;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_standard_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_d6_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  add_standard_error_reduce_ea(self, error);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix_A)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 = ZERO_d6_ea();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)4U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_d0(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_1c1(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_39_03(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[4U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_2b1(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b1(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_as_ntt[i] = call_mut_73_1c1(&lvalue););
  sample_vector_cbd_then_ntt_3b1(error_as_ntt, prf_input, domain_separator);
  compute_As_plus_e_d0(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_b4_d0(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
*/
static void call_mut_7b_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U]) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret[i] = call_mut_b4_d0(&lvalue););
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.clone_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static inline libcrux_ml_kem_polynomial_PolynomialRingElement_1d clone_c1_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d lit;
  libcrux_ml_kem_vector_portable_vector_type_PortableVector ret[16U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)16U, self->coefficients, ret,
      libcrux_ml_kem_vector_portable_vector_type_PortableVector, void *);
  memcpy(lit.coefficients, ret,
         (size_t)16U *
             sizeof(libcrux_ml_kem_vector_portable_vector_type_PortableVector));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static void transpose_a_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ind_cpa_a[4U][4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U][4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[4U][4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, call_mut_7b_d0(A[i]););
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d _a_i[4U][4U]; memcpy(
          _a_i, A,
          (size_t)4U *
              sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
      KRML_MAYBE_FOR4(
          i1, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i1;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
              clone_c1_ea(&ind_cpa_a[j][i0]);
          A[i0][j] = uu____0;););
  memcpy(ret, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_151(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c1(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[4U][4U];
  memcpy(uu____0, out->public_key.ind_cpa_public_key.A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[4U][4U];
  transpose_a_d0(uu____0, A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____1[4U][4U];
  memcpy(uu____1, A,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
  memcpy(out->public_key.ind_cpa_public_key.A, uu____1,
         (size_t)4U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]));
  uint8_t pk_serialized[1568U];
  serialize_public_key_ff(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      pk_serialized);
  uint8_t uu____2[32U];
  H_4a_ac(Eurydice_array_to_slice((size_t)1568U, pk_serialized, uint8_t),
          uu____2);
  memcpy(out->public_key.public_key_hash, uu____2,
         (size_t)32U * sizeof(uint8_t));
  uint8_t uu____3[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____3);
  memcpy(out->private_key.implicit_rejection_value, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
*/
static void encaps_prepare_03(Eurydice_slice randomness, Eurydice_slice pk_hash,
                              uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  uint8_t ret0[64U];
  G_4a_ac(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[4size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_080_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d fst[4U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d snd;
} tuple_080;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_f1_851(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_dd_851(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_3b1(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1) {
  uint8_t prf_inputs[4U][33U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(prf_inputs, domain_separator);
  uint8_t prf_outputs[4U][128U];
  PRFxN_4a_44(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          sample_from_binomial_distribution_a0(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_a6(Eurydice_slice input, uint8_t ret[128U]) {
  uint8_t digest[128U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)128U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_4a_440(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_a8_d0(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)2U),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)3U));
      zeta_i[0U] = zeta_i[0U] - (size_t)3U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->coefficients[round] =
          libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
          libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
              re->coefficients[round],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->coefficients[round] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    inv_ntt_layer_int_vec_step_reduce_ea(
        libcrux_ml_kem_vector_portable_vector_type_PortableVector a,
        libcrux_ml_kem_vector_portable_vector_type_PortableVector b,
        int16_t zeta_r) {
  libcrux_ml_kem_vector_portable_vector_type_PortableVector a_minus_b =
      libcrux_ml_kem_vector_portable_sub_b8(b, &a);
  a = libcrux_ml_kem_vector_portable_barrett_reduce_b8(
      libcrux_ml_kem_vector_portable_add_b8(a, &b));
  b = libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
      a_minus_b, zeta_r);
  return (KRML_CLITERAL(
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2){.fst = a,
                                                                    .snd = b});
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_ea(
    size_t *zeta_i, libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re,
    size_t layer) {
  size_t step = (size_t)1U << (uint32_t)layer;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U] = zeta_i[0U] - (size_t)1U;
    size_t offset = round * step * (size_t)2U;
    size_t offset_vec =
        offset / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
    size_t step_vec =
        step / LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
    for (size_t i = offset_vec; i < offset_vec + step_vec; i++) {
      size_t j = i;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2 uu____0 =
          inv_ntt_layer_int_vec_step_reduce_ea(
              re->coefficients[j], re->coefficients[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      libcrux_ml_kem_vector_portable_vector_type_PortableVector x = uu____0.fst;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector y = uu____0.snd;
      re->coefficients[j] = x;
      re->coefficients[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_ea(&zeta_i, re);
  invert_ntt_at_layer_2_ea(&zeta_i, re);
  invert_ntt_at_layer_3_ea(&zeta_i, re);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_ea(re);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
                myself->coefficients[j], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector sum =
        libcrux_ml_kem_vector_portable_add_b8(coefficient_normal_form,
                                              &error->coefficients[j]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum);
    myself->coefficients[j] = red;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_d6_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error) {
  add_error_reduce_ea(self, error);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*a_as_ntt)[4U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  result[i] = call_mut_a8_d0(&lvalue););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)4U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1d[4U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)4U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_d0(&result[i1], &product);
    }
    invert_ntt_montgomery_d0(&result[i1]);
    add_error_reduce_d6_ea(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
compress_ef(libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10,
            libcrux_secrets_int_as_u16_f5(a.elements[i0])));
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector compress_b8_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return compress_ef(a);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
compress_c4(libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)11,
            libcrux_secrets_int_as_u16_f5(a.elements[i0])));
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector compress_b8_c4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return compress_c4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_54(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[352U]) {
  uint8_t serialized[352U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        compress_b8_c4(
            libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
                re->coefficients[i0]));
    uint8_t bytes[22U];
    libcrux_ml_kem_vector_portable_serialize_11_b8(coefficient, bytes);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(serialized, (size_t)22U * i0,
                                    (size_t)22U * i0 + (size_t)22U, uint8_t *),
        Eurydice_array_to_slice((size_t)22U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)352U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_82(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[352U]) {
  uint8_t uu____0[352U];
  compress_then_serialize_11_54(re, uu____0);
  memcpy(ret, uu____0, (size_t)352U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- OUT_LEN= 1408
- COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_u_2f(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d input[4U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)4U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t *);
    uint8_t ret[352U];
    compress_then_serialize_ring_element_u_82(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)352U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_080
encrypt_c1_851(Eurydice_slice randomness,
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix)[4U],
               Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_f1_851(&lvalue););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b1(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_1[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_1[i] = call_mut_dd_851(&lvalue););
  uint8_t domain_separator =
      sample_ring_element_cbd_3b1(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_4a_440(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u[4U];
  compute_vector_u_d0(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[4U];
  memcpy(
      uu____0, u,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  compress_then_serialize_u_2f(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d copy_of_r_as_ntt[4U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  tuple_080 lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  lit.snd = error_2;
  return lit;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_message_ea(uint8_t *serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector
          coefficient_compressed =
              libcrux_ml_kem_vector_portable_deserialize_1_b8(
                  Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                              (size_t)2U * i0 + (size_t)2U,
                                              uint8_t *));
      libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
          libcrux_ml_kem_vector_portable_decompress_1_b8(
              coefficient_compressed);
      re.coefficients[i0] = uu____0;);
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
add_message_error_reduce_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
                result.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector sum1 =
        libcrux_ml_kem_vector_portable_add_b8(myself->coefficients[i0],
                                              &message->coefficients[i0]);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector sum2 =
        libcrux_ml_kem_vector_portable_add_b8(coefficient_normal_form, &sum1);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum2);
    result.coefficients[i0] = red;
  }
  return result;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
add_message_error_reduce_d6_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d result) {
  return add_message_error_reduce_ea(self, message, result);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_ring_element_v_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_d0(&result, &product););
  invert_ntt_montgomery_d0(&result);
  return add_message_error_reduce_d6_ea(error_2, message, result);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
compress_d1(libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4,
            libcrux_secrets_int_as_u16_f5(a.elements[i0])));
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector compress_b8_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return compress_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        compress_b8_d1(to_unsigned_field_modulus_ea(re.coefficients[i0]));
    uint8_t bytes[8U];
    libcrux_ml_kem_vector_portable_serialize_4_b8(coefficient, bytes);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *),
        Eurydice_array_to_slice((size_t)8U, bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
compress_f4(libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)5,
            libcrux_secrets_int_as_u16_f5(a.elements[i0])));
    a.elements[i0] = uu____0;
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress_b8
with const generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector compress_b8_f4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return compress_f4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re,
    Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficients =
        compress_b8_f4(
            libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
                re.coefficients[i0]));
    uint8_t bytes[10U];
    libcrux_ml_kem_vector_portable_serialize_5_b8(coefficients, bytes);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t *),
        Eurydice_array_to_slice((size_t)10U, bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
- OUT_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, Eurydice_slice out) {
  compress_then_serialize_5_ea(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_00(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      compute_ring_element_v_d0(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_00(v, ciphertext);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_unpacked_2a1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af *public_key,
    uint8_t *message, Eurydice_slice randomness, uint8_t ret[1568U]) {
  uint8_t ciphertext[1568U] = {0U};
  tuple_080 uu____0 =
      encrypt_c1_851(randomness, public_key->A,
                     Eurydice_array_to_subslice3(ciphertext, (size_t)0U,
                                                 (size_t)1408U, uint8_t *));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[4U];
  memcpy(
      r_as_ntt, uu____0.fst,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____1 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____2 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____3 = &error_2;
  uint8_t *uu____4 = message;
  encrypt_c2_00(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  memcpy(ret, ciphertext, (size_t)1568U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- VECTOR_U_BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_fa libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  encaps_prepare_03(Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
                    Eurydice_array_to_slice(
                        (size_t)32U, public_key->public_key_hash, uint8_t),
                    hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  uint8_t ciphertext[1568U];
  encrypt_unpacked_2a1(&public_key->ind_cpa_public_key, randomness,
                       pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext uu____2 =
      libcrux_ml_kem_types_from_e0_af(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_fa lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_35_00(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a.elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 10
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_b8_ef(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return decompress_ciphertext_coefficient_ef(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_10_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_10_b8(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        decompress_ciphertext_coefficient_b8_ef(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_c4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)11);
    decompressed = decompressed >> (uint32_t)((int32_t)11 + (int32_t)1);
    a.elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 11
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_b8_c4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return decompress_ciphertext_coefficient_c4(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_11_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)22U,
                                 i0 * (size_t)22U + (size_t)22U, uint8_t *);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_11_b8(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        decompress_ciphertext_coefficient_b8_c4(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_ring_element_u_5e(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_5e(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ea(&zeta_i, re);
  ntt_at_layer_2_ea(&zeta_i, re);
  ntt_at_layer_1_ea(&zeta_i, re);
  poly_barrett_reduce_d6_ea(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_00(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u_as_ntt[i] = call_mut_35_00(&lvalue););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1568U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)11U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U,
        uint8_t *);
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_5e(u_bytes);
    ntt_vector_u_5e(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a.elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 4
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_b8_d1(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return decompress_ciphertext_coefficient_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_4_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        libcrux_ml_kem_vector_portable_deserialize_4_b8(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        decompress_ciphertext_coefficient_b8_d1(coefficient);
    re.coefficients[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_f4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.elements[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)5);
    decompressed = decompressed >> (uint32_t)((int32_t)5 + (int32_t)1);
    a.elements[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.decompress_ciphertext_coefficient_b8 with const
generics
- COEFFICIENT_BITS= 5
*/
static libcrux_ml_kem_vector_portable_vector_type_PortableVector
decompress_ciphertext_coefficient_b8_f4(
    libcrux_ml_kem_vector_portable_vector_type_PortableVector a) {
  return decompress_ciphertext_coefficient_f4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_5_ea(Eurydice_slice serialized) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)10U,
                                 i0 * (size_t)10U + (size_t)10U, uint8_t *);
    re.coefficients[i0] =
        libcrux_ml_kem_vector_portable_deserialize_5_b8(bytes);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____1 =
        decompress_ciphertext_coefficient_b8_f4(re.coefficients[i0]);
    re.coefficients[i0] = uu____1;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
- COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_ring_element_v_ff(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
subtract_reduce_ea(libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector
        coefficient_normal_form =
            libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
                b.coefficients[i0], (int16_t)1441);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector diff =
        libcrux_ml_kem_vector_portable_sub_b8(myself->coefficients[i0],
                                              &coefficient_normal_form);
    libcrux_ml_kem_vector_portable_vector_type_PortableVector red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(diff);
    b.coefficients[i0] = red;
  }
  return b;
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
subtract_reduce_d6_ea(libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d b) {
  return subtract_reduce_ea(self, b);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_message_d0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_d0(&result, &product););
  invert_ntt_montgomery_d0(&result);
  return subtract_reduce_d6_ea(v, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_ea(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, uint8_t ret[32U]) {
  uint8_t serialized[32U] = {0U};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
          to_unsigned_field_modulus_ea(re.coefficients[i0]);
      libcrux_ml_kem_vector_portable_vector_type_PortableVector
          coefficient_compressed =
              libcrux_ml_kem_vector_portable_compress_1_b8(coefficient);
      uint8_t bytes[2U]; libcrux_ml_kem_vector_portable_serialize_1_b8(
          coefficient_compressed, bytes);
      Eurydice_slice_copy(
          Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                      (size_t)2U * i0 + (size_t)2U, uint8_t *),
          Eurydice_array_to_slice((size_t)2U, bytes, uint8_t), uint8_t););
  memcpy(ret, serialized, (size_t)32U * sizeof(uint8_t));
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_unpacked_7d(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[4U];
  deserialize_then_decompress_u_00(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      deserialize_then_decompress_ring_element_v_ff(
          Eurydice_array_to_subslice_from((size_t)1568U, ciphertext,
                                          (size_t)1408U, uint8_t, size_t,
                                          uint8_t[]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message =
      compute_message_d0(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ea(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_9e(Eurydice_slice input, uint8_t ret[32U]) {
  uint8_t digest[32U] = {0U};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, digest, uint8_t), input);
  memcpy(ret, digest, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 4
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_4a_44(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_511(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_7d(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_4a_ac(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_7f(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_4a_44(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t expected_ciphertext[1568U];
  encrypt_unpacked_2a1(&key_pair->public_key.ind_cpa_public_key, decrypted,
                       pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
          Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_d0(
    void **_) {
  return ZERO_d6_ea();
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_d0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[4U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  deserialized_pk[i] = call_mut_0b_d0(&lvalue););
  deserialize_ring_elements_reduced_d0(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_ff(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[4U];
  deserialize_ring_elements_reduced_out_d0(
      Eurydice_array_to_subslice_to(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1568U];
  serialize_public_key_ff(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]),
      public_key_serialized);
  return Eurydice_array_eq((size_t)1568U, public_key, public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_60(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  uint8_t t[32U];
  H_4a_ac(Eurydice_array_to_subslice3(
              private_key->value, (size_t)384U * (size_t)4U,
              (size_t)768U * (size_t)4U + (size_t)32U, uint8_t *),
          t);
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)4U + (size_t)32U,
      (size_t)768U * (size_t)4U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_b5(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_60(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair1024
generate_keypair_ea1(Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af private_key =
      default_70_d0();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af public_key =
      default_8b_d0();
  generate_keypair_unpacked_1c1(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_00(&public_key, &private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_60(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[3168U]) {
  uint8_t out[3168U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
      private_key, public_key, implicit_rejection_value, out);
  memcpy(ret, out, (size_t)3168U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_151(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_ea1(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1536U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1536U * sizeof(uint8_t));
  uint8_t public_key[1568U];
  memcpy(public_key, uu____0.snd, (size_t)1568U * sizeof(uint8_t));
  uint8_t secret_key_serialized[3168U];
  serialize_kem_secret_key_60(
      Eurydice_array_to_slice((size_t)1536U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[3168U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_83 private_key =
      libcrux_ml_kem_types_from_77_39(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_83 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1568U];
  memcpy(copy_of_public_key, public_key, (size_t)1568U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_94(
      uu____2, libcrux_ml_kem_types_from_fd_af(copy_of_public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_39_03(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af
    build_unpacked_public_key_3f1(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af
      unpacked_public_key = default_8b_d0();
  build_unpacked_public_key_mut_3f1(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_2a1(Eurydice_slice public_key,
                                        uint8_t *message,
                                        Eurydice_slice randomness,
                                        uint8_t ret[1568U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af
      unpacked_public_key = build_unpacked_public_key_3f1(public_key);
  uint8_t ret0[1568U];
  encrypt_unpacked_2a1(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)1568U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE void kdf_39_60(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_fa libcrux_ml_kem_ind_cca_encapsulate_ca1(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_39_03(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t ret0[32U];
  H_4a_ac(Eurydice_array_to_slice(
              (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_4a_ac(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1568U];
  encrypt_2a1(Eurydice_array_to_slice(
                  (size_t)1568U,
                  libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t),
              randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1568U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1568U * sizeof(uint8_t));
  tuple_fa lit;
  lit.fst = libcrux_ml_kem_types_from_e0_af(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_39_60(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_7d(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_7d(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_af
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret0[i] = call_mut_0b_7d(&lvalue););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)4U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  deserialize_vector_d0(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_7d(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
void libcrux_ml_kem_ind_cca_decapsulate_621(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_7d(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_4a_ac(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1600U];
  libcrux_ml_kem_utils_into_padded_array_7f(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_4a_44(Eurydice_array_to_slice((size_t)1600U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[1568U];
  encrypt_2a1(ind_cpa_public_key, decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_39_60(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_39_60(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_a0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash_cf
shake128_init_absorb_final_fd(uint8_t (*input)[34U]) {
  libcrux_ml_kem_hash_functions_portable_PortableHash_cf shake128_state;
  libcrux_sha3_generic_keccak_KeccakState_17 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.shake128_state, repeat_expression,
         (size_t)2U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.shake128_state[i0],
          Eurydice_array_to_slice((size_t)34U, input[i0], uint8_t)););
  return shake128_state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final_4a with const
generics
- K= 2
*/
libcrux_ml_kem_hash_functions_portable_PortableHash_cf
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
    uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_fd(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_fd(
    libcrux_ml_kem_hash_functions_portable_PortableHash_cf *st,
    uint8_t ret[2U][504U]) {
  uint8_t out[2U][504U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)504U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks_4a
with const generics
- K= 2
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
    libcrux_ml_kem_hash_functions_portable_PortableHash_cf *self,
    uint8_t ret[2U][504U]) {
  shake128_squeeze_first_three_blocks_fd(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_64(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block with const
generics
- K= 2
*/
static KRML_MUSTINLINE void shake128_squeeze_next_block_fd(
    libcrux_ml_kem_hash_functions_portable_PortableHash_cf *st,
    uint8_t ret[2U][168U]) {
  uint8_t out[2U][168U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)168U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block_4a with const
generics
- K= 2
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
    libcrux_ml_kem_hash_functions_portable_PortableHash_cf *self,
    uint8_t ret[2U][168U]) {
  shake128_squeeze_next_block_fd(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_640(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_e7_2b0(
    int16_t tupled_args[272U]) {
  int16_t s[272U];
  memcpy(s, tupled_args, (size_t)272U * sizeof(int16_t));
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE void sample_from_xof_2b0(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U]) {
  size_t sampled_coefficients[2U] = {0U};
  int16_t out[2U][272U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_PortableHash_cf xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
          seeds);
  uint8_t randomness0[2U][504U];
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
      &xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_64(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[2U][168U];
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
          &xof_state, randomness);
      done = sample_from_uniform_distribution_next_640(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[2U][272U];
  memcpy(copy_of_out, out, (size_t)2U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  ret0[i] = call_mut_e7_2b0(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_2b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*A_transpose)[2U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[2U][34U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d sampled[2U];
      sample_from_xof_2b0(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)2U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1d sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.H_4a
with const generics
- K= 2
*/
static KRML_MUSTINLINE void H_4a_fd(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_portable_H(input, ret);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_73(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
        *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice_to((size_t)800U, public_key->value,
                                    (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a0(
      uu____0, unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)800U, public_key->value,
                                      (size_t)768U, uint8_t, size_t, uint8_t[]),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____2)[2U] =
      unpacked_public_key->ind_cpa_public_key.A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)800U, public_key->value,
                                      (size_t)768U, uint8_t, size_t, uint8_t[]),
      ret);
  sample_matrix_A_2b0(uu____2, ret, false);
  uint8_t uu____3[32U];
  H_4a_fd(Eurydice_array_to_slice(
              (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key),
              uint8_t),
          uu____3);
  memcpy(unpacked_public_key->public_key_hash, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void serialize_vector_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_ea(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_mut_64(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  serialize_vector_a0(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)800U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_64(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *self,
    libcrux_ml_kem_types_MlKemPublicKey_52 *serialized) {
  serialize_public_key_mut_64(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_64(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_52 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_64(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void serialize_public_key_64(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[800U]) {
  uint8_t public_key_serialized[800U] = {0U};
  serialize_public_key_mut_64(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)800U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_52 serialized_dd_64(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *self) {
  uint8_t ret[800U];
  serialize_public_key_64(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      ret);
  return libcrux_ml_kem_types_from_fd_4d(ret);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_52
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_64(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *self) {
  return serialized_dd_64(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair512
serialize_unpacked_secret_key_86(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4 *private_key) {
  uint8_t public_key_serialized[800U];
  serialize_public_key_64(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[768U] = {0U};
  serialize_vector_a0(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)768U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[768U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[800U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair512 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)768U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)800U * sizeof(uint8_t));
  return lit;
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  uint8_t ret[32U];
  H_4a_fd(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_6d(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_fa *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      serialize_unpacked_secret_key_86(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t ind_cpa_public_key[800U];
  memcpy(ind_cpa_public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemPrivateKey_fa
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_6d(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_fa sk =
      libcrux_ml_kem_types_default_d3_2a();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_6d(self, &sk);
  return sk;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_vector_a0(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt) {
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt[i0] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_3f0(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a0(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[2U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_2b0(uu____1, ret, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_d1(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_a0(
      ind_cpa_secret_key,
      key_pair->private_key.ind_cpa_private_key.secret_as_ntt);
  build_unpacked_public_key_mut_3f0(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)768U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4
default_70_a0(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 default_8b_a0(
    void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  uu____0[i] = ZERO_d6_ea(););
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression0[2U][2U];
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[2U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)2U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d)););
  memcpy(lit.A, repeat_expression0,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
libcrux_ml_kem_ind_cca_unpacked_default_30_a0(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4){
          .ind_cpa_public_key = default_8b_a0(),
          .public_key_hash = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_a0(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_d4 uu____0 = {
      .ind_cpa_private_key = default_70_a0(), .implicit_rejection_value = {0U}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_a0()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.G_4a
with const generics
- K= 2
*/
static KRML_MUSTINLINE void G_4a_fd(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_portable_G(input, ret);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
*/
static KRML_MUSTINLINE void cpa_keygen_seed_39_10(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)2U;
  uint8_t ret0[64U];
  G_4a_fd(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_49(uint8_t (*input)[33U],
                                     uint8_t ret[2U][192U]) {
  uint8_t out[2U][192U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)192U, out[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, input[i0], uint8_t)););
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[192U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN_4a
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE void PRFxN_4a_49(uint8_t (*input)[33U],
                                        uint8_t ret[2U][192U]) {
  PRFxN_49(input, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
sample_from_binomial_distribution_1b(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_3_ea(randomness);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- ETA= 3
- ETA_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_3b0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(prf_inputs, domain_separator);
  uint8_t prf_outputs[2U][192U];
  PRFxN_4a_49(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_1b(
          Eurydice_array_to_slice((size_t)192U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_73_1c0(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself->coefficients,
                   libcrux_ml_kem_vector_portable_vector_type_PortableVector),
               libcrux_ml_kem_vector_portable_vector_type_PortableVector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->coefficients[i0],
                                              &rhs->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  add_to_ring_element_a0(self, rhs);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_As_plus_e_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix_A)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 = ZERO_d6_ea();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)2U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_a0(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_1c0(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_39_10(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[2U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_2b0(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b0(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_as_ntt[i] = call_mut_73_1c0(&lvalue););
  sample_vector_cbd_then_ntt_3b0(error_as_ntt, prf_input, domain_separator);
  compute_As_plus_e_a0(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_b4_a0(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
*/
static void call_mut_7b_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U]) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret[i] = call_mut_b4_a0(&lvalue););
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static void transpose_a_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ind_cpa_a[2U][2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U][2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[2U][2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, call_mut_7b_a0(A[i]););
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d _a_i[2U][2U]; memcpy(
          _a_i, A,
          (size_t)2U *
              sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
      KRML_MAYBE_FOR2(
          i1, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i1;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
              clone_c1_ea(&ind_cpa_a[j][i0]);
          A[i0][j] = uu____0;););
  memcpy(ret, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_150(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c0(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[2U][2U];
  memcpy(uu____0, out->public_key.ind_cpa_public_key.A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[2U][2U];
  transpose_a_a0(uu____0, A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____1[2U][2U];
  memcpy(uu____1, A,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
  memcpy(out->public_key.ind_cpa_public_key.A, uu____1,
         (size_t)2U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]));
  uint8_t pk_serialized[800U];
  serialize_public_key_64(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      pk_serialized);
  uint8_t uu____2[32U];
  H_4a_fd(Eurydice_array_to_slice((size_t)800U, pk_serialized, uint8_t),
          uu____2);
  memcpy(out->public_key.public_key_hash, uu____2,
         (size_t)32U * sizeof(uint8_t));
  uint8_t uu____3[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____3);
  memcpy(out->private_key.implicit_rejection_value, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
*/
static void encaps_prepare_10(Eurydice_slice randomness, Eurydice_slice pk_hash,
                              uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  uint8_t ret0[64U];
  G_4a_fd(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[2size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_35_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d fst[2U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d snd;
} tuple_35;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_f1_850(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_dd_850(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_490(uint8_t (*input)[33U],
                                      uint8_t ret[2U][128U]) {
  uint8_t out[2U][128U] = {{0U}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, out[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, input[i0], uint8_t)););
  memcpy(ret, out, (size_t)2U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN_4a
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_4a_490(uint8_t (*input)[33U],
                                         uint8_t ret[2U][128U]) {
  PRFxN_490(input, ret);
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_3b0(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1) {
  uint8_t prf_inputs[2U][33U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(prf_inputs, domain_separator);
  uint8_t prf_outputs[2U][128U];
  PRFxN_4a_490(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          sample_from_binomial_distribution_a0(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_4a_490(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_a8_a0(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_ea(&zeta_i, re);
  invert_ntt_at_layer_2_ea(&zeta_i, re);
  invert_ntt_at_layer_3_ea(&zeta_i, re);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_ea(re);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void compute_vector_u_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*a_as_ntt)[2U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  result[i] = call_mut_a8_a0(&lvalue););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)2U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1d[2U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)2U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_a0(&result[i1], &product);
    }
    invert_ntt_montgomery_a0(&result[i1]);
    add_error_reduce_d6_ea(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_ff(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[320U]) {
  uint8_t serialized[320U] = {0U};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector coefficient =
        compress_b8_ef(to_unsigned_field_modulus_ea(re->coefficients[i0]));
    uint8_t bytes[20U];
    libcrux_ml_kem_vector_portable_serialize_10_b8(coefficient, bytes);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(serialized, (size_t)20U * i0,
                                    (size_t)20U * i0 + (size_t)20U, uint8_t *),
        Eurydice_array_to_slice((size_t)20U, bytes, uint8_t), uint8_t);
  }
  memcpy(ret, serialized, (size_t)320U * sizeof(uint8_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_fe(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re, uint8_t ret[320U]) {
  uint8_t uu____0[320U];
  compress_then_serialize_10_ff(re, uu____0);
  memcpy(ret, uu____0, (size_t)320U * sizeof(uint8_t));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- OUT_LEN= 640
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_u_6d(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d input[2U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)2U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t *);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_fe(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- C1_LEN= 640
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_35
encrypt_c1_850(Eurydice_slice randomness,
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix)[2U],
               Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_f1_850(&lvalue););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b0(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_1[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_1[i] = call_mut_dd_850(&lvalue););
  uint8_t domain_separator =
      sample_ring_element_cbd_3b0(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_4a_490(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u[2U];
  compute_vector_u_a0(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[2U];
  memcpy(
      uu____0, u,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  compress_then_serialize_u_6d(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d copy_of_r_as_ntt[2U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  tuple_35 lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  lit.snd = error_2;
  return lit;
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_ring_element_v_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_a0(&result, &product););
  invert_ntt_montgomery_a0(&result);
  return add_message_error_reduce_d6_ea(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_86(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, Eurydice_slice out) {
  compress_then_serialize_4_ea(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_86(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      compute_ring_element_v_a0(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_86(v, ciphertext);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_LEN= 640
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_unpacked_2a0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 *public_key,
    uint8_t *message, Eurydice_slice randomness, uint8_t ret[768U]) {
  uint8_t ciphertext[768U] = {0U};
  tuple_35 uu____0 =
      encrypt_c1_850(randomness, public_key->A,
                     Eurydice_array_to_subslice3(ciphertext, (size_t)0U,
                                                 (size_t)640U, uint8_t *));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[2U];
  memcpy(
      r_as_ntt, uu____0.fst,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____1 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____2 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____3 = &error_2;
  uint8_t *uu____4 = message;
  encrypt_c2_86(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  memcpy(ret, ciphertext, (size_t)768U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- CIPHERTEXT_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_41 libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  encaps_prepare_10(Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
                    Eurydice_array_to_slice(
                        (size_t)32U, public_key->public_key_hash, uint8_t),
                    hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  uint8_t ciphertext[768U];
  encrypt_unpacked_2a0(&public_key->ind_cpa_public_key, randomness,
                       pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_1a uu____2 =
      libcrux_ml_kem_types_from_e0_d0(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_41 lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_35_86(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_ring_element_u_0a(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_0a(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)7U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  ntt_at_layer_3_ea(&zeta_i, re);
  ntt_at_layer_2_ea(&zeta_i, re);
  ntt_at_layer_1_ea(&zeta_i, re);
  poly_barrett_reduce_d6_ea(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_86(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u_as_ntt[i] = call_mut_35_86(&lvalue););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)768U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_0a(u_bytes);
    ntt_vector_u_0a(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_ring_element_v_64(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_ea(serialized);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_message_a0(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_a0(&result, &product););
  invert_ntt_montgomery_a0(&result);
  return subtract_reduce_d6_ea(v, result);
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_unpacked_d1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[2U];
  deserialize_then_decompress_u_86(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      deserialize_then_decompress_ring_element_v_64(
          Eurydice_array_to_subslice_from((size_t)768U, ciphertext,
                                          (size_t)640U, uint8_t, size_t,
                                          uint8_t[]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message =
      compute_message_a0(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ea(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 2
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_4a_49(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_510(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_d1(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_4a_fd(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_4d(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_4a_49(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t expected_ciphertext[768U];
  encrypt_unpacked_2a0(&key_pair->public_key.ind_cpa_public_key, decrypted,
                       pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
          Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 2
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_a0(
    void **_) {
  return ZERO_d6_ea();
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_a0(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[2U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  deserialized_pk[i] = call_mut_0b_a0(&lvalue););
  deserialize_ring_elements_reduced_a0(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_64(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[2U];
  deserialize_ring_elements_reduced_out_a0(
      Eurydice_array_to_subslice_to(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[800U];
  serialize_public_key_64(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]),
      public_key_serialized);
  return Eurydice_array_eq((size_t)800U, public_key, public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_30(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key) {
  uint8_t t[32U];
  H_4a_fd(Eurydice_array_to_subslice3(
              private_key->value, (size_t)384U * (size_t)2U,
              (size_t)768U * (size_t)2U + (size_t)32U, uint8_t *),
          t);
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)2U + (size_t)32U,
      (size_t)768U * (size_t)2U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_fb(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_30(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- PRIVATE_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair512
generate_keypair_ea0(Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4 private_key =
      default_70_a0();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 public_key =
      default_8b_a0();
  generate_keypair_unpacked_1c0(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_86(&public_key, &private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
- SERIALIZED_KEY_LEN= 1632
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_30(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[1632U]) {
  uint8_t out[1632U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
      private_key, public_key, implicit_rejection_value, out);
  memcpy(ret, out, (size_t)1632U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_ind_cca_generate_keypair_150(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_ea0(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[768U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)768U * sizeof(uint8_t));
  uint8_t public_key[800U];
  memcpy(public_key, uu____0.snd, (size_t)800U * sizeof(uint8_t));
  uint8_t secret_key_serialized[1632U];
  serialize_kem_secret_key_30(
      Eurydice_array_to_slice((size_t)768U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1632U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_fa private_key =
      libcrux_ml_kem_types_from_77_2a(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_fa uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[800U];
  memcpy(copy_of_public_key, public_key, (size_t)800U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_fa(
      uu____2, libcrux_ml_kem_types_from_fd_4d(copy_of_public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
*/
static KRML_MUSTINLINE void entropy_preprocess_39_10(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4
    build_unpacked_public_key_3f0(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4
      unpacked_public_key = default_8b_a0();
  build_unpacked_public_key_mut_3f0(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_LEN= 640
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_2a0(Eurydice_slice public_key,
                                        uint8_t *message,
                                        Eurydice_slice randomness,
                                        uint8_t ret[768U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4
      unpacked_public_key = build_unpacked_public_key_3f0(public_key);
  uint8_t ret0[768U];
  encrypt_unpacked_2a0(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)768U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE void kdf_39_30(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_41 libcrux_ml_kem_ind_cca_encapsulate_ca0(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_39_10(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t ret0[32U];
  H_4a_fd(Eurydice_array_to_slice(
              (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_4a_fd(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[768U];
  encrypt_2a0(Eurydice_array_to_slice(
                  (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key),
                  uint8_t),
              randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[768U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)768U * sizeof(uint8_t));
  tuple_41 lit;
  lit.fst = libcrux_ml_kem_types_from_e0_d0(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_39_30(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_d1(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
- CIPHERTEXT_SIZE= 768
- VECTOR_U_ENCODED_SIZE= 640
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_d1(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_d4
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret0[i] = call_mut_0b_d1(&lvalue););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)2U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  deserialize_vector_a0(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_d1(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- CIPHERTEXT_SIZE= 768
- T_AS_NTT_ENCODED_SIZE= 768
- C1_SIZE= 640
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 800
*/
void libcrux_ml_kem_ind_cca_decapsulate_620(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_d1(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_4a_fd(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[800U];
  libcrux_ml_kem_utils_into_padded_array_4d(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_4a_49(Eurydice_array_to_slice((size_t)800U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[768U];
  encrypt_2a0(ind_cpa_public_key, decrypted, pseudorandomness,
              expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_39_30(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_39_30(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 See [deserialize_ring_elements_reduced_out].
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_1b(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *deserialized_pk) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(public_key, uint8_t) /
               LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_slice ring_element = Eurydice_slice_subslice3(
        public_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
            LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_hash_functions_portable_PortableHash_88
shake128_init_absorb_final_e0(uint8_t (*input)[34U]) {
  libcrux_ml_kem_hash_functions_portable_PortableHash_88 shake128_state;
  libcrux_sha3_generic_keccak_KeccakState_17 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.shake128_state, repeat_expression,
         (size_t)3U * sizeof(libcrux_sha3_generic_keccak_KeccakState_17));
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.shake128_state[i0],
          Eurydice_array_to_slice((size_t)34U, input[i0], uint8_t)););
  return shake128_state;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final_4a with const
generics
- K= 3
*/
libcrux_ml_kem_hash_functions_portable_PortableHash_88
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
    uint8_t (*input)[34U]) {
  return shake128_init_absorb_final_e0(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_first_three_blocks_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *st,
    uint8_t ret[3U][504U]) {
  uint8_t out[3U][504U] = {{0U}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)504U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[504U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks_4a
with const generics
- K= 3
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *self,
    uint8_t ret[3U][504U]) {
  shake128_squeeze_first_three_blocks_e0(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_89(
    uint8_t (*randomness)[504U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block with const
generics
- K= 3
*/
static KRML_MUSTINLINE void shake128_squeeze_next_block_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *st,
    uint8_t ret[3U][168U]) {
  uint8_t out[3U][168U] = {{0U}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->shake128_state[i0],
          Eurydice_array_to_slice((size_t)168U, out[i0], uint8_t)););
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[168U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_next_block_4a with const
generics
- K= 3
*/
void libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
    libcrux_ml_kem_hash_functions_portable_PortableHash_88 *self,
    uint8_t ret[3U][168U]) {
  shake128_squeeze_next_block_e0(self, ret);
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_890(
    uint8_t (*randomness)[168U], size_t *sampled_coefficients,
    int16_t (*out)[272U]) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(randomness[i1], r * (size_t)24U,
                                          r * (size_t)24U + (size_t)24U,
                                          uint8_t *),
              Eurydice_array_to_subslice3(
                  out[i1], sampled_coefficients[i1],
                  sampled_coefficients[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients[uu____0] =
              sampled_coefficients[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
This function found in impl {core::ops::function::FnMut<(@Array<i16, 272usize>),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::sampling::sample_from_xof::closure<Vector,
Hasher, K>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof.call_mut_e7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_e7_2b(
    int16_t tupled_args[272U]) {
  int16_t s[272U];
  memcpy(s, tupled_args, (size_t)272U * sizeof(int16_t));
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_2b(
    uint8_t (*seeds)[34U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  size_t sampled_coefficients[3U] = {0U};
  int16_t out[3U][272U] = {{0U}};
  libcrux_ml_kem_hash_functions_portable_PortableHash_88 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
          seeds);
  uint8_t randomness0[3U][504U];
  libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
      &xof_state, randomness0);
  bool done = sample_from_uniform_distribution_next_89(
      randomness0, sampled_coefficients, out);
  while (true) {
    if (done) {
      break;
    } else {
      uint8_t randomness[3U][168U];
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
          &xof_state, randomness);
      done = sample_from_uniform_distribution_next_890(
          randomness, sampled_coefficients, out);
    }
  }
  /* Passing arrays by value in Rust generates a copy in C */
  int16_t copy_of_out[3U][272U];
  memcpy(copy_of_out, out, (size_t)3U * sizeof(int16_t[272U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  ret0[i] = call_mut_e7_2b(copy_of_out[i]););
  memcpy(
      ret, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_2b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*A_transpose)[3U],
    uint8_t *seed, bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      uint8_t seeds[3U][34U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)34U, seed, seeds[i], uint8_t, void *););
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds[j][32U] = (uint8_t)i1; seeds[j][33U] = (uint8_t)j;);
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d sampled[3U];
      sample_from_xof_2b(seeds, sampled);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(
                   Eurydice_array_to_slice(
                       (size_t)3U, sampled,
                       libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
           i++) {
        size_t j = i;
        libcrux_ml_kem_polynomial_PolynomialRingElement_1d sample = sampled[j];
        if (transpose) {
          A_transpose[j][i1] = sample;
        } else {
          A_transpose[i1][j] = sample;
        }
      });
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.H_4a
with const generics
- K= 3
*/
static KRML_MUSTINLINE void H_4a_e0(Eurydice_slice input, uint8_t ret[32U]) {
  libcrux_ml_kem_hash_functions_portable_H(input, ret);
}

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_0a(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 =
      Eurydice_array_to_subslice_to((size_t)1184U, public_key->value,
                                    (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_1b(
      uu____0, unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  uint8_t uu____1[32U];
  libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      uu____1);
  memcpy(unpacked_public_key->ind_cpa_public_key.seed_for_A, uu____1,
         (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____2)[3U] =
      unpacked_public_key->ind_cpa_public_key.A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key->value,
                                      (size_t)1152U, uint8_t, size_t,
                                      uint8_t[]),
      ret);
  sample_matrix_A_2b(uu____2, ret, false);
  uint8_t uu____3[32U];
  H_4a_e0(Eurydice_array_to_slice(
              (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key),
              uint8_t),
          uu____3);
  memcpy(unpacked_public_key->public_key_hash, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_11
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *
libcrux_ml_kem_ind_cca_unpacked_public_key_11_1b(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return &self->public_key;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.clone_91
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static inline libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
clone_91_1b(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)3U, self->t_as_ntt, uu____0,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d, void *);
  uint8_t uu____1[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->seed_for_A, uu____1, uint8_t, void *);
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U][3U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)3U, self->A, ret,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U], void *);
  memcpy(lit.A, ret,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  return lit;
}

/**
This function found in impl {core::clone::Clone for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_d7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_clone_d7_1b(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 lit;
  lit.ind_cpa_public_key = clone_91_1b(&self->ind_cpa_public_key);
  uint8_t ret[32U];
  core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)32U, self->public_key_hash, ret, uint8_t, void *);
  memcpy(lit.public_key_hash, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void serialize_vector_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *key,
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, key,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = key[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    uint8_t ret[384U];
    serialize_uncompressed_ring_element_ea(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)384U, ret, uint8_t), uint8_t);
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t *serialized) {
  serialize_vector_1b(
      t_as_ntt,
      Eurydice_array_to_subslice3(
          serialized, (size_t)0U,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t *));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)1184U, serialized,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      seed_for_a, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  serialize_public_key_mut_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_89(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPublicKey_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_89(&self->public_key,
                                                       serialized);
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_89(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    Eurydice_slice seed_for_a, uint8_t ret[1184U]) {
  uint8_t public_key_serialized[1184U] = {0U};
  serialize_public_key_mut_89(t_as_ntt, seed_for_a, public_key_serialized);
  memcpy(ret, public_key_serialized, (size_t)1184U * sizeof(uint8_t));
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE libcrux_ml_kem_types_MlKemPublicKey_30 serialized_dd_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  uint8_t ret[1184U];
  serialize_public_key_89(
      self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      ret);
  return libcrux_ml_kem_types_from_fd_d0(ret);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_30
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_89(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  return serialized_dd_89(&self->public_key);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.serialize_unpacked_secret_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static libcrux_ml_kem_utils_extraction_helper_Keypair768
serialize_unpacked_secret_key_6c(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key) {
  uint8_t public_key_serialized[1184U];
  serialize_public_key_89(
      public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, public_key->seed_for_A, uint8_t),
      public_key_serialized);
  uint8_t secret_key_serialized[1152U] = {0U};
  serialize_vector_1b(
      private_key->secret_as_ntt,
      Eurydice_array_to_slice((size_t)1152U, secret_key_serialized, uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[1152U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key_serialized[1184U];
  memcpy(copy_of_public_key_serialized, public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_utils_extraction_helper_Keypair768 lit;
  memcpy(lit.fst, copy_of_secret_key_serialized,
         (size_t)1152U * sizeof(uint8_t));
  memcpy(lit.snd, copy_of_public_key_serialized,
         (size_t)1184U * sizeof(uint8_t));
  return lit;
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key_mut
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
void libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t *serialized) {
  size_t pointer = (size_t)0U;
  uint8_t *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  uint8_t *uu____3 = serialized;
  size_t uu____4 = pointer;
  size_t uu____5 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____3, uu____4, uu____5 + Eurydice_slice_len(public_key, uint8_t),
          uint8_t *),
      public_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(public_key, uint8_t);
  Eurydice_slice uu____6 = Eurydice_array_to_subslice3(
      serialized, pointer, pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
      uint8_t *);
  uint8_t ret[32U];
  H_4a_e0(public_key, ret);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, ret, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  uint8_t *uu____7 = serialized;
  size_t uu____8 = pointer;
  size_t uu____9 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____7, uu____8,
          uu____9 + Eurydice_slice_len(implicit_rejection_value, uint8_t),
          uint8_t *),
      implicit_rejection_value, uint8_t);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
void libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_43(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self,
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      serialize_unpacked_secret_key_6c(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t ind_cpa_public_key[1184U];
  memcpy(ind_cpa_public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, self->private_key.implicit_rejection_value, uint8_t),
      serialized->value);
}

/**
This function found in impl
{libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPrivateKey_d9
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_43(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  libcrux_ml_kem_types_MlKemPrivateKey_d9 sk =
      libcrux_ml_kem_types_default_d3_28();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_43(self, &sk);
  return sk;
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_vector
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_vector_1b(
    Eurydice_slice secret_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt[i0] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key_mut
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void build_unpacked_public_key_mut_3f(
    Eurydice_slice public_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_slice_subslice_to(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_1b(uu____0, unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[3U] =
      unpacked_public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed, ret);
  sample_matrix_A_2b(uu____1, ret, false);
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
void libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_42(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_1b(
      ind_cpa_secret_key,
      key_pair->private_key.ind_cpa_private_key.secret_as_ntt);
  build_unpacked_public_key_mut_3f(ind_cpa_public_key,
                                   &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->public_key.ind_cpa_public_key.seed_for_A,
          uint8_t),
      Eurydice_slice_subslice_from(ind_cpa_public_key, (size_t)1152U, uint8_t,
                                   size_t, uint8_t[]),
      uint8_t);
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_70
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
default_70_1b(void) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 lit;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(
      lit.secret_as_ntt, repeat_expression,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.default_8b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 default_8b_1b(
    void) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  uu____0[i] = ZERO_d6_ea(););
  uint8_t uu____1[32U] = {0U};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit;
  memcpy(
      lit.t_as_ntt, uu____0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  memcpy(lit.seed_for_A, uu____1, (size_t)32U * sizeof(uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression0[3U][3U];
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U,
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d repeat_expression[3U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(repeat_expression0[i0], repeat_expression,
             (size_t)3U *
                 sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d)););
  memcpy(lit.A, repeat_expression0,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  return lit;
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
libcrux_ml_kem_ind_cca_unpacked_default_30_1b(void) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0){
          .ind_cpa_public_key = default_8b_1b(),
          .public_key_hash = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                              0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}});
}

/**
This function found in impl {core::default::Default for
libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_1b(void) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_a0 uu____0 = {
      .ind_cpa_private_key = default_70_1b(), .implicit_rejection_value = {0U}};
  return (KRML_CLITERAL(
      libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked){
      .private_key = uu____0,
      .public_key = libcrux_ml_kem_ind_cca_unpacked_default_30_1b()});
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.G_4a
with const generics
- K= 3
*/
static KRML_MUSTINLINE void G_4a_e0(Eurydice_slice input, uint8_t ret[64U]) {
  libcrux_ml_kem_hash_functions_portable_G(input, ret);
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.cpa_keygen_seed_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static KRML_MUSTINLINE void cpa_keygen_seed_39_9c(
    Eurydice_slice key_generation_seed, uint8_t ret[64U]) {
  uint8_t seed[33U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  uint8_t ret0[64U];
  G_4a_e0(Eurydice_array_to_slice((size_t)33U, seed, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_41(uint8_t (*input)[33U],
                                     uint8_t ret[3U][128U]) {
  uint8_t out[3U][128U] = {{0U}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, out[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, input[i0], uint8_t)););
  memcpy(ret, out, (size_t)3U * sizeof(uint8_t[128U]));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN_4a
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRFxN_4a_41(uint8_t (*input)[33U],
                                        uint8_t ret[3U][128U]) {
  PRFxN_41(input, ret);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_3b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re_as_ntt,
    uint8_t *prf_input, uint8_t domain_separator) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  PRFxN_4a_41(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt[i0] = sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt[i0]););
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, ETA1, ETA1_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1,
TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_73 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_73_1c(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
 sum of their constituent coefficients.
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *myself,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)16U, myself->coefficients,
                   libcrux_ml_kem_vector_portable_vector_type_PortableVector),
               libcrux_ml_kem_vector_portable_vector_type_PortableVector);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_vector_portable_vector_type_PortableVector uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->coefficients[i0],
                                              &rhs->coefficients[i0]);
    myself->coefficients[i0] = uu____0;
  }
}

/**
This function found in impl
{libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_to_ring_element_d6
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void add_to_ring_element_d6_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *self,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *rhs) {
  add_to_ring_element_1b(self, rhs);
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_As_plus_e
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix_A)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *s_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, matrix_A,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = matrix_A[i0];
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 = ZERO_d6_ea();
    t_as_ntt[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice(
                      (size_t)3U, row,
                      libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i1++) {
      size_t j = i1;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *matrix_element =
          &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt[j]);
      add_to_ring_element_d6_1b(&t_as_ntt[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt[i0], &error_as_ntt[i0]);
  }
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_1c(
    Eurydice_slice key_generation_seed,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key) {
  uint8_t hashed[64U];
  cpa_keygen_seed_39_9c(key_generation_seed, hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d(*uu____1)[3U] =
      public_key->A;
  uint8_t ret[34U];
  libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A, ret);
  sample_matrix_A_2b(uu____1, ret, true);
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error,
                                            prf_input);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b(private_key->secret_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_as_ntt[i] = call_mut_73_1c(&lvalue););
  sample_vector_cbd_then_ntt_3b(error_as_ntt, prf_input, domain_separator);
  compute_As_plus_e_1b(public_key->t_as_ntt, public_key->A,
                       private_key->secret_as_ntt, error_as_ntt);
  uint8_t uu____2[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, uint8_t[32U],
                           core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____2);
  memcpy(public_key->seed_for_A, uu____2, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.closure.call_mut_b4 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_b4_1b(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
@Array<libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1], K>> for
libcrux_ml_kem::ind_cca::unpacked::transpose_a::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.unpacked.transpose_a.call_mut_7b with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static void call_mut_7b_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret[i] = call_mut_b4_1b(&lvalue););
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static void transpose_a_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ind_cpa_a[3U][3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U][3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[3U][3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, call_mut_7b_1b(A[i]););
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d _a_i[3U][3U]; memcpy(
          _a_i, A,
          (size_t)3U *
              sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
      KRML_MAYBE_FOR3(
          i1, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i1;
          libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
              clone_c1_ea(&ind_cpa_a[j][i0]);
          A[i0][j] = uu____0;););
  memcpy(ret, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
}

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void libcrux_ml_kem_ind_cca_unpacked_generate_keypair_15(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c(ind_cpa_keypair_randomness,
                               &out->private_key.ind_cpa_private_key,
                               &out->public_key.ind_cpa_public_key);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U][3U];
  memcpy(uu____0, out->public_key.ind_cpa_public_key.A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d A[3U][3U];
  transpose_a_1b(uu____0, A);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____1[3U][3U];
  memcpy(uu____1, A,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  memcpy(out->public_key.ind_cpa_public_key.A, uu____1,
         (size_t)3U *
             sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]));
  uint8_t pk_serialized[1184U];
  serialize_public_key_89(
      out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice(
          (size_t)32U, out->public_key.ind_cpa_public_key.seed_for_A, uint8_t),
      pk_serialized);
  uint8_t uu____2[32U];
  H_4a_e0(Eurydice_array_to_slice((size_t)1184U, pk_serialized, uint8_t),
          uu____2);
  memcpy(out->public_key.public_key_hash, uu____2,
         (size_t)32U * sizeof(uint8_t));
  uint8_t uu____3[32U];
  core_result_Result_fb dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           uint8_t[32U], core_array_TryFromSliceError);
  core_result_unwrap_26_b3(dst, uu____3);
  memcpy(out->private_key.implicit_rejection_value, uu____3,
         (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static void encaps_prepare_9c(Eurydice_slice randomness, Eurydice_slice pk_hash,
                              uint8_t ret[64U]) {
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(randomness, to_hash);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  uint8_t ret0[64U];
  G_4a_e0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), ret0);
  memcpy(ret, ret0, (size_t)64U * sizeof(uint8_t));
}

/**
A monomorphic instance of K.
with types libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[3size_t],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_ed_s {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d fst[3U];
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d snd;
} tuple_ed;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure<Vector, Hasher,
K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_f1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_f1_85(
    void **_) {
  return ZERO_d6_ea();
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1, ETA1_RANDOMNESS_SIZE,
ETA2, ETA2_RANDOMNESS_SIZE>[TraitClause@0, TraitClause@1, TraitClause@2,
TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1.call_mut_dd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_dd_85(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
*/
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_3b(
    uint8_t *prf_input, uint8_t domain_separator,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1) {
  uint8_t prf_inputs[3U][33U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  core_array__core__clone__Clone_for__Array_T__N___clone(
                      (size_t)33U, prf_input, prf_inputs[i], uint8_t, void *););
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(prf_inputs, domain_separator);
  uint8_t prf_outputs[3U][128U];
  PRFxN_4a_41(prf_inputs, prf_outputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0 =
          sample_from_binomial_distribution_a0(
              Eurydice_array_to_slice((size_t)128U, prf_outputs[i0], uint8_t));
      error_1[i0] = uu____0;);
  return domain_separator;
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_4a_410(Eurydice_slice input,
                                       uint8_t ret[128U]) {
  PRF_a6(input, ret);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::matrix::compute_vector_u::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u.call_mut_a8
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_a8_1b(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *re) {
  size_t zeta_i =
      LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_ea(&zeta_i, re);
  invert_ntt_at_layer_2_ea(&zeta_i, re);
  invert_ntt_at_layer_3_ea(&zeta_i, re);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)4U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)5U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)6U);
  invert_ntt_at_layer_4_plus_ea(&zeta_i, re, (size_t)7U);
  poly_barrett_reduce_d6_ea(re);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*a_as_ntt)[3U],
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_1,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  result[i] = call_mut_a8_1b(&lvalue););
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice(
                    (size_t)3U, a_as_ntt,
                    libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]),
                libcrux_ml_kem_polynomial_PolynomialRingElement_1d[3U]);
       i0++) {
    size_t i1 = i0;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *row = a_as_ntt[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice(
                     (size_t)3U, row,
                     libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
                 libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
         i++) {
      size_t j = i;
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d *a_element = &row[j];
      libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt[j]);
      add_to_ring_element_d6_1b(&result[i1], &product);
    }
    invert_ntt_montgomery_1b(&result[i1]);
    add_error_reduce_d6_ea(&result[i1], &error_1[i1]);
  }
  memcpy(
      ret, result,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- OUT_LEN= 960
- COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_u_43(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d input[3U],
    Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice(
                   (size_t)3U, input,
                   libcrux_ml_kem_polynomial_PolynomialRingElement_1d),
               libcrux_ml_kem_polynomial_PolynomialRingElement_1d);
       i++) {
    size_t i0 = i;
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re = input[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *);
    uint8_t ret[320U];
    compress_then_serialize_ring_element_u_fe(&re, ret);
    Eurydice_slice_copy(
        uu____0, Eurydice_array_to_slice((size_t)320U, ret, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE tuple_ed
encrypt_c1_85(Eurydice_slice randomness,
              libcrux_ml_kem_polynomial_PolynomialRingElement_1d (*matrix)[3U],
              Eurydice_slice ciphertext) {
  uint8_t prf_input[33U];
  libcrux_ml_kem_utils_into_padded_array_c8(randomness, prf_input);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  r_as_ntt[i] = call_mut_f1_85(&lvalue););
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b(r_as_ntt, prf_input, 0U);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_1[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  error_1[i] = call_mut_dd_85(&lvalue););
  uint8_t domain_separator =
      sample_ring_element_cbd_3b(prf_input, domain_separator0, error_1);
  prf_input[32U] = domain_separator;
  uint8_t prf_output[128U];
  PRF_4a_410(Eurydice_array_to_slice((size_t)33U, prf_input, uint8_t),
             prf_output);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 =
      sample_from_binomial_distribution_a0(
          Eurydice_array_to_slice((size_t)128U, prf_output, uint8_t));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u[3U];
  compute_vector_u_1b(matrix, r_as_ntt, error_1, u);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d uu____0[3U];
  memcpy(
      uu____0, u,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  compress_then_serialize_u_43(uu____0, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d copy_of_r_as_ntt[3U];
  memcpy(
      copy_of_r_as_ntt, r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  tuple_ed lit;
  memcpy(
      lit.fst, copy_of_r_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  lit.snd = error_2;
  return lit;
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_ring_element_v
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_ring_element_v_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *message) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&t_as_ntt[i0], &r_as_ntt[i0]);
                  add_to_ring_element_d6_1b(&result, &product););
  invert_ntt_montgomery_1b(&result);
  return add_message_error_reduce_d6_ea(error_2, message, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
- OUT_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d re, Eurydice_slice out) {
  compress_then_serialize_4_ea(re, out);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_c2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_6c(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *t_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *r_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *error_2,
    uint8_t *message, Eurydice_slice ciphertext) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      compute_ring_element_v_1b(t_as_ntt, r_as_ntt, error_2,
                                &message_as_ring_element);
  compress_then_serialize_ring_element_v_6c(v, ciphertext);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_unpacked_2a(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    uint8_t *message, Eurydice_slice randomness, uint8_t ret[1088U]) {
  uint8_t ciphertext[1088U] = {0U};
  tuple_ed uu____0 =
      encrypt_c1_85(randomness, public_key->A,
                    Eurydice_array_to_subslice3(ciphertext, (size_t)0U,
                                                (size_t)960U, uint8_t *));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d r_as_ntt[3U];
  memcpy(
      r_as_ntt, uu____0.fst,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d error_2 = uu____0.snd;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____1 =
      public_key->t_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____2 = r_as_ntt;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____3 = &error_2;
  uint8_t *uu____4 = message;
  encrypt_c2_6c(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  memcpy(ret, ciphertext, (size_t)1088U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_c2 libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t *randomness) {
  uint8_t hashed[64U];
  encaps_prepare_9c(Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
                    Eurydice_array_to_slice(
                        (size_t)32U, public_key->public_key_hash, uint8_t),
                    hashed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  uint8_t ciphertext[1088U];
  encrypt_unpacked_2a(&public_key->ind_cpa_public_key, randomness,
                      pseudorandomness, ciphertext);
  uint8_t shared_secret_array[32U] = {0U};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext uu____2 =
      libcrux_ml_kem_types_from_e0_80(copy_of_ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_shared_secret_array[32U];
  memcpy(copy_of_shared_secret_array, shared_secret_array,
         (size_t)32U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = uu____2;
  memcpy(lit.snd, copy_of_shared_secret_array, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::ind_cpa::deserialize_then_decompress_u::closure<Vector, K,
CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u.call_mut_35 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_35_6c(
    void **_) {
  return ZERO_d6_ea();
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.deserialize_then_decompress_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_6c(
    uint8_t *ciphertext,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  u_as_ntt[i] = call_mut_35_6c(&lvalue););
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)1088U, ciphertext, uint8_t),
               uint8_t) /
               (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_slice u_bytes = Eurydice_array_to_subslice3(
        ciphertext,
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U),
        i0 * (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
              (size_t)10U / (size_t)8U) +
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U,
        uint8_t *);
    u_as_ntt[i0] = deserialize_then_decompress_ring_element_u_0a(u_bytes);
    ntt_vector_u_0a(&u_as_ntt[i0]);
  }
  memcpy(
      ret, u_as_ntt,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
deserialize_then_decompress_ring_element_v_89(Eurydice_slice serialized) {
  return deserialize_then_decompress_4_ea(serialized);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_ml_kem.matrix.compute_message
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE libcrux_ml_kem_polynomial_PolynomialRingElement_1d
compute_message_1b(
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *v,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *secret_as_ntt,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d *u_as_ntt) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d result = ZERO_d6_ea();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  libcrux_ml_kem_polynomial_PolynomialRingElement_1d product =
                      ntt_multiply_d6_ea(&secret_as_ntt[i0], &u_as_ntt[i0]);
                  add_to_ring_element_d6_1b(&result, &product););
  invert_ntt_montgomery_1b(&result);
  return subtract_reduce_d6_ea(v, result);
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_unpacked_42(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 *secret_key,
    uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d u_as_ntt[3U];
  deserialize_then_decompress_u_6c(ciphertext, u_as_ntt);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d v =
      deserialize_then_decompress_ring_element_v_89(
          Eurydice_array_to_subslice_from((size_t)1088U, ciphertext,
                                          (size_t)960U, uint8_t, size_t,
                                          uint8_t[]));
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d message =
      compute_message_1b(&v, secret_key->secret_as_ntt, u_as_ntt);
  uint8_t ret0[32U];
  compress_then_serialize_message_ea(message, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::hash_functions::Hash<K> for
libcrux_ml_kem::hash_functions::portable::PortableHash<K>}
*/
/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF_4a
with const generics
- K= 3
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_4a_41(Eurydice_slice input, uint8_t ret[32U]) {
  PRF_9e(input, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
void libcrux_ml_kem_ind_cca_unpacked_decapsulate_51(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  uint8_t decrypted[32U];
  decrypt_unpacked_42(&key_pair->private_key.ind_cpa_private_key,
                      ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U, key_pair->public_key.public_key_hash,
                              uint8_t),
      uint8_t);
  uint8_t hashed[64U];
  G_4a_e0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(
      Eurydice_array_to_slice(
          (size_t)32U, key_pair->private_key.implicit_rejection_value, uint8_t),
      to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret[32U];
  PRF_4a_41(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t expected_ciphertext[1088U];
  encrypt_unpacked_2a(&key_pair->public_key.ind_cpa_public_key, decrypted,
                      pseudorandomness, expected_ciphertext);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t));
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_ml_kem::serialize::deserialize_ring_elements_reduced_out::closure<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out.call_mut_0b with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_1b(
    void **_) {
  return ZERO_d6_ea();
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_ring_elements_reduced_out with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_out_1b(
    Eurydice_slice public_key,
    libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret[3U]) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  deserialized_pk[i] = call_mut_0b_1b(&lvalue););
  deserialize_ring_elements_reduced_1b(public_key, deserialized_pk);
  memcpy(
      ret, deserialized_pk,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_89(uint8_t *public_key) {
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d deserialized_pk[3U];
  deserialize_ring_elements_reduced_out_1b(
      Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      deserialized_pk);
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d *uu____0 = deserialized_pk;
  uint8_t public_key_serialized[1184U];
  serialize_public_key_89(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]),
      public_key_serialized);
  return Eurydice_array_eq((size_t)1184U, public_key, public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_d6(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  uint8_t t[32U];
  H_4a_e0(Eurydice_array_to_subslice3(
              private_key->value, (size_t)384U * (size_t)3U,
              (size_t)768U * (size_t)3U + (size_t)32U, uint8_t *),
          t);
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key->value, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, t, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_37(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *_ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_d6(private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE libcrux_ml_kem_utils_extraction_helper_Keypair768
generate_keypair_ea(Eurydice_slice key_generation_seed) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0 private_key =
      default_70_1b();
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 public_key =
      default_8b_1b();
  generate_keypair_unpacked_1c(key_generation_seed, &private_key, &public_key);
  return serialize_unpacked_secret_key_6c(&public_key, &private_key);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.serialize_kem_secret_key
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_d6(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value, uint8_t ret[2400U]) {
  uint8_t out[2400U] = {0U};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      private_key, public_key, implicit_rejection_value, out);
  memcpy(ret, out, (size_t)2400U * sizeof(uint8_t));
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_15(uint8_t *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_ea(ind_cpa_keypair_randomness);
  uint8_t ind_cpa_private_key[1152U];
  memcpy(ind_cpa_private_key, uu____0.fst, (size_t)1152U * sizeof(uint8_t));
  uint8_t public_key[1184U];
  memcpy(public_key, uu____0.snd, (size_t)1184U * sizeof(uint8_t));
  uint8_t secret_key_serialized[2400U];
  serialize_kem_secret_key_d6(
      Eurydice_array_to_slice((size_t)1152U, ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, public_key, uint8_t),
      implicit_rejection_value, secret_key_serialized);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_secret_key_serialized[2400U];
  memcpy(copy_of_secret_key_serialized, secret_key_serialized,
         (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 private_key =
      libcrux_ml_kem_types_from_77_28(copy_of_secret_key_serialized);
  libcrux_ml_kem_types_MlKemPrivateKey_d9 uu____2 = private_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_public_key[1184U];
  memcpy(copy_of_public_key, public_key, (size_t)1184U * sizeof(uint8_t));
  return libcrux_ml_kem_types_from_17_74(
      uu____2, libcrux_ml_kem_types_from_fd_d0(copy_of_public_key));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.entropy_preprocess_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_39_9c(Eurydice_slice randomness,
                                                     uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      randomness, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.build_unpacked_public_key
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
    build_unpacked_public_key_3f(Eurydice_slice public_key) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key = default_8b_1b();
  build_unpacked_public_key_mut_3f(public_key, &unpacked_public_key);
  return unpacked_public_key;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.encrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void encrypt_2a(Eurydice_slice public_key,
                                       uint8_t *message,
                                       Eurydice_slice randomness,
                                       uint8_t ret[1088U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key = build_unpacked_public_key_3f(public_key);
  uint8_t ret0[1088U];
  encrypt_unpacked_2a(&unpacked_public_key, message, randomness, ret0);
  memcpy(ret, ret0, (size_t)1088U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::variant::Variant for
libcrux_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_ml_kem.variant.kdf_39
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void kdf_39_d6(Eurydice_slice shared_secret,
                                      uint8_t ret[32U]) {
  uint8_t out[32U] = {0U};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, out, uint8_t),
                      shared_secret, uint8_t);
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
tuple_c2 libcrux_ml_kem_ind_cca_encapsulate_ca(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  uint8_t randomness0[32U];
  entropy_preprocess_39_9c(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t), randomness0);
  uint8_t to_hash[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, randomness0, uint8_t), to_hash);
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  uint8_t ret0[32U];
  H_4a_e0(Eurydice_array_to_slice(
              (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key),
              uint8_t),
          ret0);
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, ret0, uint8_t), uint8_t);
  uint8_t hashed[64U];
  G_4a_e0(Eurydice_array_to_slice((size_t)64U, to_hash, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t ciphertext[1088U];
  encrypt_2a(Eurydice_array_to_slice(
                 (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key),
                 uint8_t),
             randomness0, pseudorandomness, ciphertext);
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_ciphertext[1088U];
  memcpy(copy_of_ciphertext, ciphertext, (size_t)1088U * sizeof(uint8_t));
  tuple_c2 lit;
  lit.fst = libcrux_ml_kem_types_from_e0_80(copy_of_ciphertext);
  uint8_t ret[32U];
  kdf_39_d6(shared_secret, ret);
  memcpy(lit.snd, ret, (size_t)32U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt.call_mut_0b
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static libcrux_ml_kem_polynomial_PolynomialRingElement_1d call_mut_0b_42(
    void **_) {
  return ZERO_d6_ea();
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.decrypt
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_42(Eurydice_slice secret_key,
                                       uint8_t *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPrivateKeyUnpacked_a0
      secret_key_unpacked;
  libcrux_ml_kem_polynomial_PolynomialRingElement_1d ret0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  ret0[i] = call_mut_0b_42(&lvalue););
  memcpy(
      secret_key_unpacked.secret_as_ntt, ret0,
      (size_t)3U * sizeof(libcrux_ml_kem_polynomial_PolynomialRingElement_1d));
  deserialize_vector_1b(secret_key, secret_key_unpacked.secret_as_ntt);
  uint8_t ret1[32U];
  decrypt_unpacked_42(&secret_key_unpacked, ciphertext, ret1);
  memcpy(ret, ret1, (size_t)32U * sizeof(uint8_t));
}

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_variant_MlKem with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
void libcrux_ml_kem_ind_cca_decapsulate_62(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key->value, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  uint8_t decrypted[32U];
  decrypt_42(ind_cpa_secret_key, ciphertext->value, decrypted);
  uint8_t to_hash0[64U];
  libcrux_ml_kem_utils_into_padded_array_24(
      Eurydice_array_to_slice((size_t)32U, decrypted, uint8_t), to_hash0);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  uint8_t hashed[64U];
  G_4a_e0(Eurydice_array_to_slice((size_t)64U, to_hash0, uint8_t), hashed);
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  uint8_t to_hash[1120U];
  libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value, to_hash);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  uint8_t implicit_rejection_shared_secret0[32U];
  PRF_4a_41(Eurydice_array_to_slice((size_t)1120U, to_hash, uint8_t),
            implicit_rejection_shared_secret0);
  uint8_t expected_ciphertext[1088U];
  encrypt_2a(ind_cpa_public_key, decrypted, pseudorandomness,
             expected_ciphertext);
  uint8_t implicit_rejection_shared_secret[32U];
  kdf_39_d6(Eurydice_array_to_slice((size_t)32U,
                                    implicit_rejection_shared_secret0, uint8_t),
            implicit_rejection_shared_secret);
  uint8_t shared_secret[32U];
  kdf_39_d6(shared_secret0, shared_secret);
  uint8_t ret0[32U];
  libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, implicit_rejection_shared_secret,
                              uint8_t),
      ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}
