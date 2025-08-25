/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: 3c77f1ac8116257d0c416fdac562edfa178b860b
 * Karamel: 354791911c6b40d15a41cda7a0e3560da1cf31a1
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: b894d22937e1239a34ec32e0ebf3d6f8892331a0
 */

#include "internal/libcrux_mlkem_portable.h"

#include "internal/libcrux_core.h"
#include "libcrux_core.h"
#include "libcrux_sha3_portable.h"

KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
libcrux_ml_kem_hash_functions_portable_G(Eurydice_slice input) {
  libcrux_sha3_Sha3_512Digest digest = {.data = {0U}};
  libcrux_sha3_portable_sha512(
      Eurydice_array_to_slice((size_t)64U, &digest, uint8_t), input);
  return digest;
}

KRML_MUSTINLINE Eurydice_arr_60
libcrux_ml_kem_hash_functions_portable_H(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  libcrux_sha3_portable_sha256(
      Eurydice_array_to_slice((size_t)32U, &digest, uint8_t), input);
  return digest;
}

#define ZETAS_TIMES_MONTGOMERY_R                                     \
  ((KRML_CLITERAL(Eurydice_arr_49){                                  \
      .data = {(int16_t) - 1044, (int16_t) - 758,  (int16_t) - 359,  \
               (int16_t) - 1517, (int16_t)1493,    (int16_t)1422,    \
               (int16_t)287,     (int16_t)202,     (int16_t) - 171,  \
               (int16_t)622,     (int16_t)1577,    (int16_t)182,     \
               (int16_t)962,     (int16_t) - 1202, (int16_t) - 1474, \
               (int16_t)1468,    (int16_t)573,     (int16_t) - 1325, \
               (int16_t)264,     (int16_t)383,     (int16_t) - 829,  \
               (int16_t)1458,    (int16_t) - 1602, (int16_t) - 130,  \
               (int16_t) - 681,  (int16_t)1017,    (int16_t)732,     \
               (int16_t)608,     (int16_t) - 1542, (int16_t)411,     \
               (int16_t) - 205,  (int16_t) - 1571, (int16_t)1223,    \
               (int16_t)652,     (int16_t) - 552,  (int16_t)1015,    \
               (int16_t) - 1293, (int16_t)1491,    (int16_t) - 282,  \
               (int16_t) - 1544, (int16_t)516,     (int16_t) - 8,    \
               (int16_t) - 320,  (int16_t) - 666,  (int16_t) - 1618, \
               (int16_t) - 1162, (int16_t)126,     (int16_t)1469,    \
               (int16_t) - 853,  (int16_t) - 90,   (int16_t) - 271,  \
               (int16_t)830,     (int16_t)107,     (int16_t) - 1421, \
               (int16_t) - 247,  (int16_t) - 951,  (int16_t) - 398,  \
               (int16_t)961,     (int16_t) - 1508, (int16_t) - 725,  \
               (int16_t)448,     (int16_t) - 1065, (int16_t)677,     \
               (int16_t) - 1275, (int16_t) - 1103, (int16_t)430,     \
               (int16_t)555,     (int16_t)843,     (int16_t) - 1251, \
               (int16_t)871,     (int16_t)1550,    (int16_t)105,     \
               (int16_t)422,     (int16_t)587,     (int16_t)177,     \
               (int16_t) - 235,  (int16_t) - 291,  (int16_t) - 460,  \
               (int16_t)1574,    (int16_t)1653,    (int16_t) - 246,  \
               (int16_t)778,     (int16_t)1159,    (int16_t) - 147,  \
               (int16_t) - 777,  (int16_t)1483,    (int16_t) - 602,  \
               (int16_t)1119,    (int16_t) - 1590, (int16_t)644,     \
               (int16_t) - 872,  (int16_t)349,     (int16_t)418,     \
               (int16_t)329,     (int16_t) - 156,  (int16_t) - 75,   \
               (int16_t)817,     (int16_t)1097,    (int16_t)603,     \
               (int16_t)610,     (int16_t)1322,    (int16_t) - 1285, \
               (int16_t) - 1465, (int16_t)384,     (int16_t) - 1215, \
               (int16_t) - 136,  (int16_t)1218,    (int16_t) - 1335, \
               (int16_t) - 874,  (int16_t)220,     (int16_t) - 1187, \
               (int16_t) - 1659, (int16_t) - 1185, (int16_t) - 1530, \
               (int16_t) - 1278, (int16_t)794,     (int16_t) - 1510, \
               (int16_t) - 854,  (int16_t) - 870,  (int16_t)478,     \
               (int16_t) - 108,  (int16_t) - 308,  (int16_t)996,     \
               (int16_t)991,     (int16_t)958,     (int16_t) - 1460, \
               (int16_t)1522,    (int16_t)1628}}))

int16_t libcrux_ml_kem_polynomial_zeta(size_t i) {
  return ZETAS_TIMES_MONTGOMERY_R.data[i];
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_serialize_deserialize_4(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)4U, uint8_t *));
  int16_t_x8 v8_15 = libcrux_ml_kem_vector_portable_serialize_deserialize_4_int(
      Eurydice_slice_subslice3(bytes, (size_t)4U, (size_t)8U, uint8_t *));
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5, v0_7.f6,
               v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd, v8_15.f3, v8_15.f4,
               v8_15.f5, v8_15.f6, v8_15.f7}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_4(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_4(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_4_b8(
    Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_4(a);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_vector_type_to_i16_array(Eurydice_arr_e2 x) {
  return x;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_to_i16_array_b8(
    Eurydice_arr_e2 x) {
  return libcrux_secrets_int_public_integers_declassify_d8_3a(
      libcrux_ml_kem_vector_portable_vector_type_to_i16_array(x));
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_slice array) {
  core_result_Result_20 dst;
  Eurydice_slice_to_array2(
      &dst, Eurydice_slice_subslice3(array, (size_t)0U, (size_t)16U, int16_t *),
      Eurydice_slice, Eurydice_arr_e2, core_array_TryFromSliceError);
  return core_result_unwrap_26_0e(dst);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_from_i16_array_b8(
    Eurydice_slice array) {
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

KRML_MUSTINLINE Eurydice_arr_77
libcrux_ml_kem_vector_portable_serialize_serialize_5(Eurydice_arr_e2 v) {
  uint8_t_x5 r0_4 = libcrux_ml_kem_vector_portable_serialize_serialize_5_int(
      Eurydice_array_to_subslice3(&v, (size_t)0U, (size_t)8U, int16_t *));
  uint8_t_x5 r5_9 = libcrux_ml_kem_vector_portable_serialize_serialize_5_int(
      Eurydice_array_to_subslice3(&v, (size_t)8U, (size_t)16U, int16_t *));
  return (KRML_CLITERAL(Eurydice_arr_77){
      .data = {r0_4.fst, r0_4.snd, r0_4.thd, r0_4.f3, r0_4.f4, r5_9.fst,
               r5_9.snd, r5_9.thd, r5_9.f3, r5_9.f4}});
}

Eurydice_arr_77 libcrux_ml_kem_vector_portable_serialize_5(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_ed(
      libcrux_ml_kem_vector_portable_serialize_serialize_5(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_77 libcrux_ml_kem_vector_portable_serialize_5_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_5(a);
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_serialize_deserialize_5(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)5U, uint8_t *));
  int16_t_x8 v8_15 = libcrux_ml_kem_vector_portable_serialize_deserialize_5_int(
      Eurydice_slice_subslice3(bytes, (size_t)5U, (size_t)10U, uint8_t *));
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5, v0_7.f6,
               v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd, v8_15.f3, v8_15.f4,
               v8_15.f5, v8_15.f6, v8_15.f7}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_5(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_5(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_5_b8(
    Eurydice_slice a) {
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_serialize_deserialize_10(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)10U, uint8_t *));
  int16_t_x8 v8_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice3(bytes, (size_t)10U, (size_t)20U, uint8_t *));
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5, v0_7.f6,
               v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd, v8_15.f3, v8_15.f4,
               v8_15.f5, v8_15.f6, v8_15.f7}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_10(
    Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_10(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_10_b8(
    Eurydice_slice a) {
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

KRML_MUSTINLINE Eurydice_arr_f3
libcrux_ml_kem_vector_portable_serialize_serialize_11(Eurydice_arr_e2 v) {
  uint8_t_x11 r0_10 = libcrux_ml_kem_vector_portable_serialize_serialize_11_int(
      Eurydice_array_to_subslice3(&v, (size_t)0U, (size_t)8U, int16_t *));
  uint8_t_x11 r11_21 =
      libcrux_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice3(&v, (size_t)8U, (size_t)16U, int16_t *));
  return (KRML_CLITERAL(Eurydice_arr_f3){
      .data = {r0_10.fst, r0_10.snd,  r0_10.thd,  r0_10.f3,   r0_10.f4,
               r0_10.f5,  r0_10.f6,   r0_10.f7,   r0_10.f8,   r0_10.f9,
               r0_10.f10, r11_21.fst, r11_21.snd, r11_21.thd, r11_21.f3,
               r11_21.f4, r11_21.f5,  r11_21.f6,  r11_21.f7,  r11_21.f8,
               r11_21.f9, r11_21.f10}});
}

Eurydice_arr_f3 libcrux_ml_kem_vector_portable_serialize_11(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_a9(
      libcrux_ml_kem_vector_portable_serialize_serialize_11(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_f3 libcrux_ml_kem_vector_portable_serialize_11_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_11(a);
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_serialize_deserialize_11(Eurydice_slice bytes) {
  int16_t_x8 v0_7 = libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
      Eurydice_slice_subslice3(bytes, (size_t)0U, (size_t)11U, uint8_t *));
  int16_t_x8 v8_15 =
      libcrux_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice3(bytes, (size_t)11U, (size_t)22U, uint8_t *));
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {v0_7.fst, v0_7.snd, v0_7.thd, v0_7.f3, v0_7.f4, v0_7.f5, v0_7.f6,
               v0_7.f7, v8_15.fst, v8_15.snd, v8_15.thd, v8_15.f3, v8_15.f4,
               v8_15.f5, v8_15.f6, v8_15.f7}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_11(
    Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_11(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_11_b8(
    Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_deserialize_11(a);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_vector_type_zero(void) {
  return libcrux_secrets_int_public_integers_classify_27_3a(
      (KRML_CLITERAL(Eurydice_arr_e2){
          .data = {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0}}));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ZERO_b8(void) {
  return libcrux_ml_kem_vector_portable_vector_type_zero();
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_vector_type_from_bytes(Eurydice_slice array) {
  Eurydice_arr_e2 elements;
  int16_t repeat_expression[16U];
  KRML_MAYBE_FOR16(i, (size_t)0U, (size_t)16U, (size_t)1U,
                   repeat_expression[i] = libcrux_secrets_int_I16((int16_t)0););
  memcpy(elements.data, repeat_expression, (size_t)16U * sizeof(int16_t));
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    elements.data[i0] =
        libcrux_secrets_int_as_i16_59(
            Eurydice_slice_index(array, (size_t)2U * i0, uint8_t, uint8_t *))
            << 8U |
        libcrux_secrets_int_as_i16_59(Eurydice_slice_index(
            array, (size_t)2U * i0 + (size_t)1U, uint8_t, uint8_t *));
  }
  return elements;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_from_bytes_b8(
    Eurydice_slice array) {
  return libcrux_ml_kem_vector_portable_vector_type_from_bytes(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&array)[0U]);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_vector_type_to_bytes(
    Eurydice_arr_e2 x, Eurydice_slice bytes) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    Eurydice_slice_index(bytes, (size_t)2U * i0, uint8_t, uint8_t *) =
        libcrux_secrets_int_as_u8_f5(x.data[i0] >> 8U);
    Eurydice_slice_index(bytes, (size_t)2U * i0 + (size_t)1U, uint8_t,
                         uint8_t *) = libcrux_secrets_int_as_u8_f5(x.data[i0]);
  }
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_ml_kem_vector_portable_to_bytes_b8(Eurydice_arr_e2 x,
                                                Eurydice_slice bytes) {
  libcrux_ml_kem_vector_portable_vector_type_to_bytes(
      x, libcrux_secrets_int_public_integers_classify_mut_slice_ba(bytes));
}

KRML_MUSTINLINE Eurydice_arr_e2 libcrux_ml_kem_vector_portable_arithmetic_add(
    Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.data[uu____0] = lhs.data[uu____0] + rhs->data[i0];
  }
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_add_b8(Eurydice_arr_e2 lhs,
                                                      Eurydice_arr_e2 *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE Eurydice_arr_e2 libcrux_ml_kem_vector_portable_arithmetic_sub(
    Eurydice_arr_e2 lhs, Eurydice_arr_e2 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs.data[uu____0] = lhs.data[uu____0] - rhs->data[i0];
  }
  return lhs;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_sub_b8(Eurydice_arr_e2 lhs,
                                                      Eurydice_arr_e2 *rhs) {
  return libcrux_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    Eurydice_arr_e2 vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.data[uu____0] = vec.data[uu____0] * c;
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_multiply_by_constant_b8(
    Eurydice_arr_e2 vec, int16_t c) {
  return libcrux_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    Eurydice_arr_e2 vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (libcrux_secrets_int_public_integers_declassify_d8_39(vec.data[i0]) >=
        (int16_t)3329) {
      size_t uu____0 = i0;
      vec.data[uu____0] = vec.data[uu____0] - (int16_t)3329;
    }
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(
    Eurydice_arr_e2 v) {
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce(Eurydice_arr_e2 vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec.data[i0]);
    vec.data[i0] = vi;
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_barrett_reduce_b8(
    Eurydice_arr_e2 vector) {
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_e2 vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.data[i0] =
        libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec.data[i0], c);
  }
  return vec;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2
libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
    Eurydice_arr_e2 vector, int16_t constant) {
  return libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vector, libcrux_secrets_int_public_integers_classify_27_39(constant));
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    Eurydice_arr_e2 vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec.data[uu____0] = vec.data[uu____0] & c;
  }
  return vec;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.arithmetic.shift_right
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE Eurydice_arr_e2 shift_right_ef(Eurydice_arr_e2 vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    vec.data[i0] = vec.data[i0] >> (uint32_t)(int32_t)15;
  }
  return vec;
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_arithmetic_to_unsigned_representative(
    Eurydice_arr_e2 a) {
  Eurydice_arr_e2 t = shift_right_ef(a);
  Eurydice_arr_e2 fm =
      libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
          t, LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  return libcrux_ml_kem_vector_portable_arithmetic_add(a, &fm);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
    Eurydice_arr_e2 a) {
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_compress_compress_1(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    a.data[i0] = libcrux_secrets_int_as_i16_59(
        libcrux_ml_kem_vector_portable_compress_compress_message_coefficient(
            libcrux_secrets_int_as_u16_f5(a.data[i0])));
  }
  return a;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_compress_1_b8(
    Eurydice_arr_e2 a) {
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

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_compress_decompress_1(Eurydice_arr_e2 a) {
  Eurydice_arr_e2 z = libcrux_ml_kem_vector_portable_vector_type_zero();
  Eurydice_arr_e2 s = libcrux_ml_kem_vector_portable_arithmetic_sub(z, &a);
  Eurydice_arr_e2 res =
      libcrux_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
          s, (int16_t)1665);
  return res;
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_decompress_1_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_compress_decompress_1(a);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_ntt_step(
    Eurydice_arr_e2 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->data[j],
          libcrux_secrets_int_public_integers_classify_27_39(zeta));
  int16_t a_minus_t = vec->data[i] - t;
  int16_t a_plus_t = vec->data[i] + t;
  vec->data[j] = a_minus_t;
  vec->data[i] = a_plus_t;
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(Eurydice_arr_e2 vec,
                                                    int16_t zeta0,
                                                    int16_t zeta1,
                                                    int16_t zeta2,
                                                    int16_t zeta3) {
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
    Eurydice_arr_e2 a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                             zeta2, zeta3);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(Eurydice_arr_e2 vec,
                                                    int16_t zeta0,
                                                    int16_t zeta1) {
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
    Eurydice_arr_e2 a, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(Eurydice_arr_e2 vec,
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
    Eurydice_arr_e2 a, int16_t zeta) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void libcrux_ml_kem_vector_portable_ntt_inv_ntt_step(
    Eurydice_arr_e2 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = vec->data[j] - vec->data[i];
  int16_t a_plus_b = vec->data[j] + vec->data[i];
  int16_t o0 = libcrux_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
      a_plus_b);
  int16_t o1 =
      libcrux_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_39(zeta));
  vec->data[i] = o0;
  vec->data[j] = o1;
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(Eurydice_arr_e2 vec,
                                                        int16_t zeta0,
                                                        int16_t zeta1,
                                                        int16_t zeta2,
                                                        int16_t zeta3) {
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
    Eurydice_arr_e2 a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
      a, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(Eurydice_arr_e2 vec,
                                                        int16_t zeta0,
                                                        int16_t zeta1) {
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
    Eurydice_arr_e2 a, int16_t zeta0, int16_t zeta1) {
  return libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0,
                                                                 zeta1);
}

KRML_MUSTINLINE Eurydice_arr_e2
libcrux_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(Eurydice_arr_e2 vec,
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
    Eurydice_arr_e2 a, int16_t zeta) {
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
    Eurydice_arr_e2 *a, Eurydice_arr_e2 *b, int16_t zeta, size_t i,
    Eurydice_arr_e2 *out) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
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
  out->data[(size_t)2U * i] = o0;
  out->data[(size_t)2U * i + (size_t)1U] = o1;
}

KRML_MUSTINLINE Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ntt_ntt_multiply(
    Eurydice_arr_e2 *lhs, Eurydice_arr_e2 *rhs, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = -zeta0;
  int16_t nzeta1 = -zeta1;
  int16_t nzeta2 = -zeta2;
  int16_t nzeta3 = -zeta3;
  Eurydice_arr_e2 out = libcrux_ml_kem_vector_portable_vector_type_zero();
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
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_ntt_multiply_b8(
    Eurydice_arr_e2 *lhs, Eurydice_arr_e2 *rhs, int16_t zeta0, int16_t zeta1,
    int16_t zeta2, int16_t zeta3) {
  return libcrux_ml_kem_vector_portable_ntt_ntt_multiply(lhs, rhs, zeta0, zeta1,
                                                         zeta2, zeta3);
}

KRML_MUSTINLINE Eurydice_arr_8b
libcrux_ml_kem_vector_portable_serialize_serialize_1(Eurydice_arr_e2 v) {
  uint8_t result0 =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v.data[0U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[1U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[2U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[3U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[4U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[5U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[6U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[7U]) << 7U;
  uint8_t result1 =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v.data[8U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[9U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[10U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[11U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[12U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[13U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[14U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v.data[15U]) << 7U;
  return (KRML_CLITERAL(Eurydice_arr_8b){.data = {result0, result1}});
}

Eurydice_arr_8b libcrux_ml_kem_vector_portable_serialize_1(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_ee0(
      libcrux_ml_kem_vector_portable_serialize_serialize_1(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_8b libcrux_ml_kem_vector_portable_serialize_1_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_1(a);
}

KRML_MUSTINLINE Eurydice_arr_e2
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
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {result0, result1, result2, result3, result4, result5, result6,
               result7, result8, result9, result10, result11, result12,
               result13, result14, result15}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_1(Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_1(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_1_b8(
    Eurydice_slice a) {
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

KRML_MUSTINLINE Eurydice_arr_c4
libcrux_ml_kem_vector_portable_serialize_serialize_4(Eurydice_arr_e2 v) {
  uint8_t_x4 result0_3 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(&v, (size_t)0U, (size_t)8U, int16_t *));
  uint8_t_x4 result4_7 =
      libcrux_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice3(&v, (size_t)8U, (size_t)16U, int16_t *));
  return (KRML_CLITERAL(Eurydice_arr_c4){
      .data = {result0_3.fst, result0_3.snd, result0_3.thd, result0_3.f3,
               result4_7.fst, result4_7.snd, result4_7.thd, result4_7.f3}});
}

Eurydice_arr_c4 libcrux_ml_kem_vector_portable_serialize_4(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_36(
      libcrux_ml_kem_vector_portable_serialize_serialize_4(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_c4 libcrux_ml_kem_vector_portable_serialize_4_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_4(a);
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

KRML_MUSTINLINE Eurydice_arr_dc
libcrux_ml_kem_vector_portable_serialize_serialize_10(Eurydice_arr_e2 v) {
  uint8_t_x5 r0_4 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(&v, (size_t)0U, (size_t)4U, int16_t *));
  uint8_t_x5 r5_9 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(&v, (size_t)4U, (size_t)8U, int16_t *));
  uint8_t_x5 r10_14 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(&v, (size_t)8U, (size_t)12U, int16_t *));
  uint8_t_x5 r15_19 = libcrux_ml_kem_vector_portable_serialize_serialize_10_int(
      Eurydice_array_to_subslice3(&v, (size_t)12U, (size_t)16U, int16_t *));
  return (KRML_CLITERAL(Eurydice_arr_dc){
      .data = {r0_4.fst,   r0_4.snd,   r0_4.thd,   r0_4.f3,   r0_4.f4,
               r5_9.fst,   r5_9.snd,   r5_9.thd,   r5_9.f3,   r5_9.f4,
               r10_14.fst, r10_14.snd, r10_14.thd, r10_14.f3, r10_14.f4,
               r15_19.fst, r15_19.snd, r15_19.thd, r15_19.f3, r15_19.f4}});
}

Eurydice_arr_dc libcrux_ml_kem_vector_portable_serialize_10(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_89(
      libcrux_ml_kem_vector_portable_serialize_serialize_10(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_dc libcrux_ml_kem_vector_portable_serialize_10_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_10(a);
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

KRML_MUSTINLINE Eurydice_arr_6d
libcrux_ml_kem_vector_portable_serialize_serialize_12(Eurydice_arr_e2 v) {
  uint8_t_x3 r0_2 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)0U, (size_t)2U, int16_t *));
  uint8_t_x3 r3_5 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)2U, (size_t)4U, int16_t *));
  uint8_t_x3 r6_8 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)4U, (size_t)6U, int16_t *));
  uint8_t_x3 r9_11 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)6U, (size_t)8U, int16_t *));
  uint8_t_x3 r12_14 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)8U, (size_t)10U, int16_t *));
  uint8_t_x3 r15_17 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)10U, (size_t)12U, int16_t *));
  uint8_t_x3 r18_20 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)12U, (size_t)14U, int16_t *));
  uint8_t_x3 r21_23 = libcrux_ml_kem_vector_portable_serialize_serialize_12_int(
      Eurydice_array_to_subslice3(&v, (size_t)14U, (size_t)16U, int16_t *));
  return (KRML_CLITERAL(Eurydice_arr_6d){
      .data = {r0_2.fst,   r0_2.snd,   r0_2.thd,   r3_5.fst,   r3_5.snd,
               r3_5.thd,   r6_8.fst,   r6_8.snd,   r6_8.thd,   r9_11.fst,
               r9_11.snd,  r9_11.thd,  r12_14.fst, r12_14.snd, r12_14.thd,
               r15_17.fst, r15_17.snd, r15_17.thd, r18_20.fst, r18_20.snd,
               r18_20.thd, r21_23.fst, r21_23.snd, r21_23.thd}});
}

Eurydice_arr_6d libcrux_ml_kem_vector_portable_serialize_12(Eurydice_arr_e2 a) {
  return libcrux_secrets_int_public_integers_declassify_d8_bd(
      libcrux_ml_kem_vector_portable_serialize_serialize_12(a));
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_6d libcrux_ml_kem_vector_portable_serialize_12_b8(
    Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_serialize_12(a);
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

KRML_MUSTINLINE Eurydice_arr_e2
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
  return (KRML_CLITERAL(Eurydice_arr_e2){
      .data = {v0_1.fst, v0_1.snd, v2_3.fst, v2_3.snd, v4_5.fst, v4_5.snd,
               v6_7.fst, v6_7.snd, v8_9.fst, v8_9.snd, v10_11.fst, v10_11.snd,
               v12_13.fst, v12_13.snd, v14_15.fst, v14_15.snd}});
}

Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_12(
    Eurydice_slice a) {
  return libcrux_ml_kem_vector_portable_serialize_deserialize_12(
      libcrux_secrets_int_public_integers_classify_ref_c5_ba(&a)[0U]);
}

/**
This function found in impl {libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_e2 libcrux_ml_kem_vector_portable_deserialize_12_b8(
    Eurydice_slice a) {
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
inline Eurydice_arr_e2 libcrux_ml_kem_vector_portable_vector_type_clone_9c(
    Eurydice_arr_e2 *self) {
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
static Eurydice_arr_b9 ZERO_d6_ea(void) {
  Eurydice_arr_b9 lit;
  Eurydice_arr_e2 repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_b8(););
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(Eurydice_arr_e2));
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
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_to_reduced_ring_element_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    Eurydice_arr_e2 coefficient =
        libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes);
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_cond_subtract_3329_b8(coefficient);
    re.data[i0] = uu____0;
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
    Eurydice_slice public_key, Eurydice_arr_0d *deserialized_pk) {
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
    Eurydice_arr_b9 uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_180
shake128_init_absorb_final_ac(Eurydice_arr_78 *input) {
  Eurydice_arr_180 shake128_state;
  Eurydice_arr_26 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_26));
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.data[i0],
          Eurydice_array_to_slice((size_t)34U, &input->data[i0], uint8_t)););
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
Eurydice_arr_180
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
    Eurydice_arr_78 *input) {
  return shake128_init_absorb_final_ac(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_ec
shake128_squeeze_first_three_blocks_ac(Eurydice_arr_180 *st) {
  Eurydice_arr_ec out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)504U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_ec
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
    Eurydice_arr_180 *self) {
  return shake128_squeeze_first_three_blocks_ac(self);
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
    Eurydice_arr_ec *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_a6
shake128_squeeze_next_block_ac(Eurydice_arr_180 *st) {
  Eurydice_arr_a6 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)168U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_a6
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
    Eurydice_arr_180 *self) {
  return shake128_squeeze_next_block_ac(self);
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
    Eurydice_arr_a6 *randomness, Eurydice_arr_33 *sampled_coefficients,
    Eurydice_arr_8a *out) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
      } else { done = false; });
  return done;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.ZERO
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static Eurydice_arr_b9 ZERO_ea(void) {
  Eurydice_arr_b9 lit;
  Eurydice_arr_e2 repeat_expression[16U];
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U,
      repeat_expression[i] = libcrux_ml_kem_vector_portable_ZERO_b8(););
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(Eurydice_arr_e2));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.from_i16_array
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9 from_i16_array_ea(Eurydice_slice a) {
  Eurydice_arr_b9 result = ZERO_ea();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 = libcrux_ml_kem_vector_portable_from_i16_array_b8(
        Eurydice_slice_subslice3(a, i0 * (size_t)16U,
                                 (i0 + (size_t)1U) * (size_t)16U, int16_t *));
    result.data[i0] = uu____0;
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
static KRML_MUSTINLINE Eurydice_arr_b9 from_i16_array_d6_ea(Eurydice_slice a) {
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
static Eurydice_arr_b9 call_mut_e7_2b1(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE Eurydice_arr_0d
sample_from_xof_2b1(Eurydice_arr_78 *seeds) {
  Eurydice_arr_33 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_8a out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_180 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_ac(
          seeds);
  Eurydice_arr_ec randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_ac(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_ff(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_ac(
              &xof_state);
      done = sample_from_uniform_distribution_next_ff0(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_0d arr_mapped_str;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_2b1(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] with const
generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_2b1(Eurydice_arr_950 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_78 seeds; Eurydice_arr_480 repeat_expression[4U];
      KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)4U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_0d sampled = sample_from_xof_2b1(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)4U, &sampled,
                                                          Eurydice_arr_b9),
                                  Eurydice_arr_b9);
           i++) {
        size_t j = i;
        Eurydice_arr_b9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
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
static KRML_MUSTINLINE Eurydice_arr_60 H_4a_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_H(input);
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
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1568U, public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_d0(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_950 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1568U, public_key, (size_t)1536U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_2b1(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_4a_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_e2
to_unsigned_field_modulus_ea(Eurydice_arr_e2 a) {
  return libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_cc
serialize_uncompressed_ring_element_ea(Eurydice_arr_b9 *re) {
  Eurydice_arr_cc serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient = to_unsigned_field_modulus_ea(re->data[i0]);
    Eurydice_arr_6d bytes =
        libcrux_ml_kem_vector_portable_serialize_12_b8(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)24U * i0,
                                    (size_t)24U * i0 + (size_t)24U, uint8_t *),
        Eurydice_array_to_slice((size_t)24U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
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
static KRML_MUSTINLINE void serialize_vector_d0(Eurydice_arr_0d *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, key, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_ea(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_0d *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_00 *serialized) {
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
    Eurydice_arr_00 *serialized) {
  serialize_public_key_mut_ff(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
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
    Eurydice_arr_00 *serialized) {
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
static KRML_MUSTINLINE Eurydice_arr_00
serialize_public_key_ff(Eurydice_arr_0d *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_00 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_ff(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
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
static KRML_MUSTINLINE Eurydice_arr_00 serialized_dd_ff(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *self) {
  return libcrux_ml_kem_types_from_fd_af(serialize_public_key_ff(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
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
Eurydice_arr_00 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_ff(
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
    Eurydice_arr_0d *private_key) {
  Eurydice_arr_00 public_key_serialized = serialize_public_key_ff(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_38 secret_key_serialized = {.data = {0U}};
  serialize_vector_d0(
      private_key,
      Eurydice_array_to_slice((size_t)1536U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair1024){
      .fst = secret_key_serialized, .snd = public_key_serialized});
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_17 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_17 *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_17 *uu____3 = serialized;
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
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_ac(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_17 *uu____7 = serialized;
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
    Eurydice_arr_17 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      serialize_unpacked_secret_key_00(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_38 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_00 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
      Eurydice_array_to_slice((size_t)1536U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
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
Eurydice_arr_17 libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_2f(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *self) {
  Eurydice_arr_17 sk = libcrux_ml_kem_types_default_d3_39();
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2f(self, &sk);
  return sk;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_to_uncompressed_ring_element_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)24U,
                                 i0 * (size_t)24U + (size_t)24U, uint8_t *);
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_deserialize_12_b8(bytes);
    re.data[i0] = uu____0;
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
    Eurydice_slice secret_key, Eurydice_arr_0d *secret_as_ntt) {
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
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
  deserialize_ring_elements_reduced_d0(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1536U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_950 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_2b1(uu____1, &lvalue, false);
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
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_d0(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_3f1(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
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
static Eurydice_arr_0d default_70_d0(void) {
  Eurydice_arr_0d lit;
  Eurydice_arr_b9 repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_b9));
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
  Eurydice_arr_0d uu____0;
  Eurydice_arr_b9 repeat_expression0[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_ea(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_b9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_0d repeat_expression1[4U];
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, Eurydice_arr_0d lit;
      Eurydice_arr_b9 repeat_expression[4U];
      KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_b9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1, (size_t)4U * sizeof(Eurydice_arr_0d));
  return lit0;
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
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af){
      .ind_cpa_public_key = default_8b_d0(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
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
      .ind_cpa_private_key = default_70_d0(),
      .implicit_rejection_value = {.data = {0U}}};
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_4a_ac(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_G(input);
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_03(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)4U;
  return G_4a_ac(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 4
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_44(Eurydice_arr_65 *input) {
  Eurydice_arr_cc0 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, &out.data[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, &input->data[i0], uint8_t)););
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_cc0 PRFxN_4a_44(Eurydice_arr_65 *input) {
  return PRFxN_44(input);
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
static KRML_MUSTINLINE Eurydice_arr_b9
sample_from_binomial_distribution_2_ea(Eurydice_slice randomness) {
  Eurydice_arr_c1 sampled_i16s = {.data = {0U}};
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
      sampled_i16s.data[(size_t)8U * chunk_number + offset] =
          outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_ea(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution_3 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
sample_from_binomial_distribution_3_ea(Eurydice_slice randomness) {
  Eurydice_arr_c1 sampled_i16s = {.data = {0U}};
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
      sampled_i16s.data[(size_t)4U * chunk_number + offset] =
          outcome_1 - outcome_2;
    }
  }
  return from_i16_array_d6_ea(
      Eurydice_array_to_slice((size_t)256U, &sampled_i16s, int16_t));
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 2
*/
static KRML_MUSTINLINE Eurydice_arr_b9
sample_from_binomial_distribution_a0(Eurydice_slice randomness) {
  return sample_from_binomial_distribution_2_ea(randomness);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_7
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_ea(Eurydice_arr_b9 *re) {
  size_t step = LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    Eurydice_arr_e2 t = libcrux_ml_kem_vector_portable_multiply_by_constant_b8(
        re->data[j + step], (int16_t)-1600);
    re->data[j + step] = libcrux_ml_kem_vector_portable_sub_b8(re->data[j], &t);
    Eurydice_arr_e2 uu____1 =
        libcrux_ml_kem_vector_portable_add_b8(re->data[j], &t);
    re->data[j] = uu____1;
  }
}

typedef struct libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2_s {
  Eurydice_arr_e2 fst;
  Eurydice_arr_e2 snd;
} libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2;

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    ntt_layer_int_vec_step_ea(Eurydice_arr_e2 a, Eurydice_arr_e2 b,
                              int16_t zeta_r) {
  Eurydice_arr_e2 t =
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
static KRML_MUSTINLINE void ntt_at_layer_4_plus_ea(size_t *zeta_i,
                                                   Eurydice_arr_b9 *re,
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
          ntt_layer_int_vec_step_ea(re->data[j], re->data[j + step_vec],
                                    libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      Eurydice_arr_e2 x = uu____0.fst;
      Eurydice_arr_e2 y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_ea(size_t *zeta_i,
                                              Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      Eurydice_arr_e2 uu____0 =
          libcrux_ml_kem_vector_portable_ntt_layer_3_step_b8(
              re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->data[round] = uu____0;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_2
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_ea(size_t *zeta_i,
                                              Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_portable_ntt_layer_2_step_b8(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] + (size_t)1U));
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_ea(size_t *zeta_i,
                                              Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] + (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_portable_ntt_layer_1_step_b8(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void poly_barrett_reduce_ea(Eurydice_arr_b9 *myself) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(myself->data[i0]);
    myself->data[i0] = uu____0;
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
static KRML_MUSTINLINE void poly_barrett_reduce_d6_ea(Eurydice_arr_b9 *self) {
  poly_barrett_reduce_ea(self);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_binomially_sampled_ring_element
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_ea(
    Eurydice_arr_b9 *re) {
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
    Eurydice_arr_0d *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_cc0 prf_outputs = PRFxN_4a_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_a0(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt->data[i0]););
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
static Eurydice_arr_b9 call_mut_73_1c1(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_b9 ntt_multiply_ea(Eurydice_arr_b9 *myself,
                                                       Eurydice_arr_b9 *rhs) {
  Eurydice_arr_b9 out = ZERO_ea();
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 = libcrux_ml_kem_vector_portable_ntt_multiply_b8(
        &myself->data[i0], &rhs->data[i0],
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)1U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)2U),
        libcrux_ml_kem_polynomial_zeta((size_t)64U + (size_t)4U * i0 +
                                       (size_t)3U));
    out.data[i0] = uu____0;
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
static KRML_MUSTINLINE Eurydice_arr_b9
ntt_multiply_d6_ea(Eurydice_arr_b9 *self, Eurydice_arr_b9 *rhs) {
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
static KRML_MUSTINLINE void add_to_ring_element_d0(Eurydice_arr_b9 *myself,
                                                   Eurydice_arr_b9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, Eurydice_arr_e2),
               Eurydice_arr_e2);
       i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
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
static KRML_MUSTINLINE void add_to_ring_element_d6_d0(Eurydice_arr_b9 *self,
                                                      Eurydice_arr_b9 *rhs) {
  add_to_ring_element_d0(self, rhs);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.to_standard_domain
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_e2
to_standard_domain_ea(Eurydice_arr_e2 vector) {
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
    Eurydice_arr_b9 *myself, Eurydice_arr_b9 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    Eurydice_arr_e2 coefficient_normal_form =
        to_standard_domain_ea(myself->data[j]);
    Eurydice_arr_e2 sum = libcrux_ml_kem_vector_portable_add_b8(
        coefficient_normal_form, &error->data[j]);
    Eurydice_arr_e2 red = libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum);
    myself->data[j] = red;
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
    Eurydice_arr_b9 *self, Eurydice_arr_b9 *error) {
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
    Eurydice_arr_0d *t_as_ntt, Eurydice_arr_950 *matrix_A,
    Eurydice_arr_0d *s_as_ntt, Eurydice_arr_0d *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, matrix_A, Eurydice_arr_0d),
               Eurydice_arr_0d);
       i++) {
    size_t i0 = i;
    Eurydice_arr_0d *row = &matrix_A->data[i0];
    Eurydice_arr_b9 uu____0 = ZERO_d6_ea();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_b9),
                  Eurydice_arr_b9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_b9 *matrix_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_d0(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
    Eurydice_slice key_generation_seed, Eurydice_arr_0d *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_03(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_950 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_2b1(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b1(private_key, &prf_input, 0U);
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_1c1(&lvalue););
  Eurydice_arr_0d error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_3b1(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_d0(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
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
static Eurydice_arr_b9 call_mut_b4_d0(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_0d call_mut_7b_d0(void **_) {
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_d0(&lvalue););
  return arr_struct;
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
static inline Eurydice_arr_b9 clone_c1_ea(Eurydice_arr_b9 *self) {
  return core_array__core__clone__Clone_for__Array_T__N___clone(
      (size_t)16U, self, Eurydice_arr_e2, Eurydice_arr_b9);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static Eurydice_arr_950 transpose_a_d0(Eurydice_arr_950 ind_cpa_a) {
  Eurydice_arr_950 arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_d0(&lvalue););
  Eurydice_arr_950 A = arr_struct;
  KRML_MAYBE_FOR4(
      i0, (size_t)0U, (size_t)4U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR4(
          i, (size_t)0U, (size_t)4U, (size_t)1U, size_t j = i;
          Eurydice_arr_b9 uu____0 = clone_c1_ea(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
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
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c1(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_950 A = transpose_a_d0(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_00 pk_serialized = serialize_public_key_ff(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_4a_ac(Eurydice_array_to_slice((size_t)1568U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]]
with const generics
- K= 4
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_03(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_4a_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[[$4size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_0c0_s {
  Eurydice_arr_0d fst;
  Eurydice_arr_b9 snd;
} tuple_0c0;

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
static Eurydice_arr_b9 call_mut_f1_851(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_b9 call_mut_dd_851(void **_) { return ZERO_d6_ea(); }

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
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_0d *error_1) {
  Eurydice_arr_65 prf_inputs;
  Eurydice_arr_3e repeat_expression[4U];
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)4U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_ac(&prf_inputs, domain_separator);
  Eurydice_arr_cc0 prf_outputs = PRFxN_4a_44(&prf_inputs);
  KRML_MAYBE_FOR4(
      i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          sample_from_binomial_distribution_a0(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
  return domain_separator;
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_a6(Eurydice_slice input) {
  Eurydice_arr_d1 digest = {.data = {0U}};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)128U, &digest, uint8_t), input);
  return digest;
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
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_4a_440(Eurydice_slice input) {
  return PRF_a6(input);
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
static Eurydice_arr_b9 call_mut_a8_d0(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_ea(size_t *zeta_i,
                                                     Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_portable_inv_ntt_layer_1_step_b8(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
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
static KRML_MUSTINLINE void invert_ntt_at_layer_2_ea(size_t *zeta_i,
                                                     Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      re->data[round] = libcrux_ml_kem_vector_portable_inv_ntt_layer_2_step_b8(
          re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]),
          libcrux_ml_kem_polynomial_zeta(zeta_i[0U] - (size_t)1U));
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;);
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_ea(size_t *zeta_i,
                                                     Eurydice_arr_b9 *re) {
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t round = i;
      zeta_i[0U] = zeta_i[0U] - (size_t)1U;
      Eurydice_arr_e2 uu____0 =
          libcrux_ml_kem_vector_portable_inv_ntt_layer_3_step_b8(
              re->data[round], libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      re->data[round] = uu____0;);
}

/**
A monomorphic instance of
libcrux_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE
    libcrux_ml_kem_vector_portable_vector_type_PortableVector_x2
    inv_ntt_layer_int_vec_step_reduce_ea(Eurydice_arr_e2 a, Eurydice_arr_e2 b,
                                         int16_t zeta_r) {
  Eurydice_arr_e2 a_minus_b = libcrux_ml_kem_vector_portable_sub_b8(b, &a);
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
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_ea(size_t *zeta_i,
                                                          Eurydice_arr_b9 *re,
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
              re->data[j], re->data[j + step_vec],
              libcrux_ml_kem_polynomial_zeta(zeta_i[0U]));
      Eurydice_arr_e2 x = uu____0.fst;
      Eurydice_arr_e2 y = uu____0.snd;
      re->data[j] = x;
      re->data[j + step_vec] = y;
    }
  }
}

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_d0(Eurydice_arr_b9 *re) {
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
static KRML_MUSTINLINE void add_error_reduce_ea(Eurydice_arr_b9 *myself,
                                                Eurydice_arr_b9 *error) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    Eurydice_arr_e2 coefficient_normal_form =
        libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
            myself->data[j], (int16_t)1441);
    Eurydice_arr_e2 sum = libcrux_ml_kem_vector_portable_add_b8(
        coefficient_normal_form, &error->data[j]);
    Eurydice_arr_e2 red = libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum);
    myself->data[j] = red;
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
static KRML_MUSTINLINE void add_error_reduce_d6_ea(Eurydice_arr_b9 *self,
                                                   Eurydice_arr_b9 *error) {
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
static KRML_MUSTINLINE Eurydice_arr_0d
compute_vector_u_d0(Eurydice_arr_950 *a_as_ntt, Eurydice_arr_0d *r_as_ntt,
                    Eurydice_arr_0d *error_1) {
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_d0(&lvalue););
  Eurydice_arr_0d result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)4U, a_as_ntt, Eurydice_arr_0d),
                Eurydice_arr_0d);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_0d *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)4U, row, Eurydice_arr_b9),
                 Eurydice_arr_b9);
         i++) {
      size_t j = i;
      Eurydice_arr_b9 *a_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_d0(&result.data[i1], &product);
    }
    invert_ntt_montgomery_d0(&result.data[i1]);
    add_error_reduce_d6_ea(&result.data[i1], &error_1->data[i1]);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE Eurydice_arr_e2 compress_ef(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)10, libcrux_secrets_int_as_u16_f5(a.data[i0])));
    a.data[i0] = uu____0;
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
static Eurydice_arr_e2 compress_b8_ef(Eurydice_arr_e2 a) {
  return compress_ef(a);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE Eurydice_arr_e2 compress_c4(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)11, libcrux_secrets_int_as_u16_f5(a.data[i0])));
    a.data[i0] = uu____0;
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
static Eurydice_arr_e2 compress_b8_c4(Eurydice_arr_e2 a) {
  return compress_c4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_11
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_11_54(Eurydice_arr_b9 *re) {
  Eurydice_arr_79 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient = compress_b8_c4(
        libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
            re->data[i0]));
    Eurydice_arr_f3 bytes =
        libcrux_ml_kem_vector_portable_serialize_11_b8(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)22U * i0,
                                    (size_t)22U * i0 + (size_t)22U, uint8_t *),
        Eurydice_array_to_slice((size_t)22U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 11
- OUT_LEN= 352
*/
static KRML_MUSTINLINE Eurydice_arr_79
compress_then_serialize_ring_element_u_82(Eurydice_arr_b9 *re) {
  return compress_then_serialize_11_54(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_2f(Eurydice_arr_0d input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)4U, &input, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)1408U / (size_t)4U),
        (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_79 lvalue = compress_then_serialize_ring_element_u_82(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)352U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_0c0 encrypt_c1_851(Eurydice_slice randomness,
                                                Eurydice_arr_950 *matrix,
                                                Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_0d arr_struct0;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_851(&lvalue););
  Eurydice_arr_0d r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b1(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_851(&lvalue););
  Eurydice_arr_0d error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_3b1(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_4a_440(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_b9 error_2 = sample_from_binomial_distribution_a0(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_0d u = compute_vector_u_d0(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_2f(u, ciphertext);
  return (KRML_CLITERAL(tuple_0c0){.fst = r_as_ntt, .snd = error_2});
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_message_ea(Eurydice_arr_60 *serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_e2 coefficient_compressed =
          libcrux_ml_kem_vector_portable_deserialize_1_b8(
              Eurydice_array_to_subslice3(serialized, (size_t)2U * i0,
                                          (size_t)2U * i0 + (size_t)2U,
                                          uint8_t *));
      Eurydice_arr_e2 uu____0 = libcrux_ml_kem_vector_portable_decompress_1_b8(
          coefficient_compressed);
      re.data[i0] = uu____0;);
  return re;
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.add_message_error_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9 add_message_error_reduce_ea(
    Eurydice_arr_b9 *myself, Eurydice_arr_b9 *message, Eurydice_arr_b9 result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient_normal_form =
        libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
            result.data[i0], (int16_t)1441);
    Eurydice_arr_e2 sum1 = libcrux_ml_kem_vector_portable_add_b8(
        myself->data[i0], &message->data[i0]);
    Eurydice_arr_e2 sum2 =
        libcrux_ml_kem_vector_portable_add_b8(coefficient_normal_form, &sum1);
    Eurydice_arr_e2 red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(sum2);
    result.data[i0] = red;
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
static KRML_MUSTINLINE Eurydice_arr_b9 add_message_error_reduce_d6_ea(
    Eurydice_arr_b9 *self, Eurydice_arr_b9 *message, Eurydice_arr_b9 result) {
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
static KRML_MUSTINLINE Eurydice_arr_b9
compute_ring_element_v_d0(Eurydice_arr_0d *t_as_ntt, Eurydice_arr_0d *r_as_ntt,
                          Eurydice_arr_b9 *error_2, Eurydice_arr_b9 *message) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
                  add_to_ring_element_d6_d0(&result, &product););
  invert_ntt_montgomery_d0(&result);
  return add_message_error_reduce_d6_ea(error_2, message, result);
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE Eurydice_arr_e2 compress_d1(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)4, libcrux_secrets_int_as_u16_f5(a.data[i0])));
    a.data[i0] = uu____0;
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
static Eurydice_arr_e2 compress_b8_d1(Eurydice_arr_e2 a) {
  return compress_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_ea(
    Eurydice_arr_b9 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient =
        compress_b8_d1(to_unsigned_field_modulus_ea(re.data[i0]));
    Eurydice_arr_c4 bytes =
        libcrux_ml_kem_vector_portable_serialize_4_b8(coefficient);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)8U * i0,
                                 (size_t)8U * i0 + (size_t)8U, uint8_t *),
        Eurydice_array_to_slice((size_t)8U, &bytes, uint8_t), uint8_t);
  }
}

/**
A monomorphic instance of libcrux_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE Eurydice_arr_e2 compress_f4(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)(int32_t)5, libcrux_secrets_int_as_u16_f5(a.data[i0])));
    a.data[i0] = uu____0;
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
static Eurydice_arr_e2 compress_b8_f4(Eurydice_arr_e2 a) {
  return compress_f4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_5
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_ea(
    Eurydice_arr_b9 re, Eurydice_slice serialized) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficients = compress_b8_f4(
        libcrux_ml_kem_vector_portable_to_unsigned_representative_b8(
            re.data[i0]));
    Eurydice_arr_77 bytes =
        libcrux_ml_kem_vector_portable_serialize_5_b8(coefficients);
    Eurydice_slice_copy(
        Eurydice_slice_subslice3(serialized, (size_t)10U * i0,
                                 (size_t)10U * i0 + (size_t)10U, uint8_t *),
        Eurydice_array_to_slice((size_t)10U, &bytes, uint8_t), uint8_t);
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
    Eurydice_arr_b9 re, Eurydice_slice out) {
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
static KRML_MUSTINLINE void encrypt_c2_00(Eurydice_arr_0d *t_as_ntt,
                                          Eurydice_arr_0d *r_as_ntt,
                                          Eurydice_arr_b9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_b9 message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  Eurydice_arr_b9 v = compute_ring_element_v_d0(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_unpacked_2a1(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_00 ciphertext = {.data = {0U}};
  tuple_0c0 uu____0 =
      encrypt_c1_851(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)1408U, uint8_t *));
  Eurydice_arr_0d r_as_ntt = uu____0.fst;
  Eurydice_arr_b9 error_2 = uu____0.snd;
  Eurydice_arr_0d *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_0d *uu____2 = &r_as_ntt;
  Eurydice_arr_b9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_00(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1568U, &ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
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
tuple_2b libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_03(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_00 ciphertext = encrypt_unpacked_2a1(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_2b){
      .fst = libcrux_ml_kem_types_from_e0_af(ciphertext),
      .snd = shared_secret_array});
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
static Eurydice_arr_b9 call_mut_35_00(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE Eurydice_arr_e2
decompress_ciphertext_coefficient_ef(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.data[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)10);
    decompressed = decompressed >> (uint32_t)((int32_t)10 + (int32_t)1);
    a.data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
static Eurydice_arr_e2 decompress_ciphertext_coefficient_b8_ef(
    Eurydice_arr_e2 a) {
  return decompress_ciphertext_coefficient_ef(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_10_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)20U,
                                 i0 * (size_t)20U + (size_t)20U, uint8_t *);
    Eurydice_arr_e2 coefficient =
        libcrux_ml_kem_vector_portable_deserialize_10_b8(bytes);
    Eurydice_arr_e2 uu____0 =
        decompress_ciphertext_coefficient_b8_ef(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE Eurydice_arr_e2
decompress_ciphertext_coefficient_c4(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.data[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)11);
    decompressed = decompressed >> (uint32_t)((int32_t)11 + (int32_t)1);
    a.data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
static Eurydice_arr_e2 decompress_ciphertext_coefficient_b8_c4(
    Eurydice_arr_e2 a) {
  return decompress_ciphertext_coefficient_c4(a);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_11_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)22U,
                                 i0 * (size_t)22U + (size_t)22U, uint8_t *);
    Eurydice_arr_e2 coefficient =
        libcrux_ml_kem_vector_portable_deserialize_11_b8(bytes);
    Eurydice_arr_e2 uu____0 =
        decompress_ciphertext_coefficient_b8_c4(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_ring_element_u_5e(Eurydice_slice serialized) {
  return deserialize_then_decompress_11_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_5e(Eurydice_arr_b9 *re) {
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
static KRML_MUSTINLINE Eurydice_arr_0d
deserialize_then_decompress_u_00(Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_00(&lvalue););
  Eurydice_arr_0d u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_5e(u_bytes);
    ntt_vector_u_5e(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE Eurydice_arr_e2
decompress_ciphertext_coefficient_d1(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.data[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)4);
    decompressed = decompressed >> (uint32_t)((int32_t)4 + (int32_t)1);
    a.data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
static Eurydice_arr_e2 decompress_ciphertext_coefficient_b8_d1(
    Eurydice_arr_e2 a) {
  return decompress_ciphertext_coefficient_d1(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_4
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_4_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes = Eurydice_slice_subslice3(
        serialized, i0 * (size_t)8U, i0 * (size_t)8U + (size_t)8U, uint8_t *);
    Eurydice_arr_e2 coefficient =
        libcrux_ml_kem_vector_portable_deserialize_4_b8(bytes);
    Eurydice_arr_e2 uu____0 =
        decompress_ciphertext_coefficient_b8_d1(coefficient);
    re.data[i0] = uu____0;
  }
  return re;
}

/**
A monomorphic instance of
libcrux_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient with
const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE Eurydice_arr_e2
decompress_ciphertext_coefficient_f4(Eurydice_arr_e2 a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed =
        libcrux_secrets_int_as_i32_f5(a.data[i0]) *
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
    decompressed = (decompressed << 1U) + ((int32_t)1 << (uint32_t)(int32_t)5);
    decompressed = decompressed >> (uint32_t)((int32_t)5 + (int32_t)1);
    a.data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
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
static Eurydice_arr_e2 decompress_ciphertext_coefficient_b8_f4(
    Eurydice_arr_e2 a) {
  return decompress_ciphertext_coefficient_f4(a);
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.deserialize_then_decompress_5
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_5_ea(Eurydice_slice serialized) {
  Eurydice_arr_b9 re = ZERO_d6_ea();
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(serialized, uint8_t) / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_slice bytes =
        Eurydice_slice_subslice3(serialized, i0 * (size_t)10U,
                                 i0 * (size_t)10U + (size_t)10U, uint8_t *);
    re.data[i0] = libcrux_ml_kem_vector_portable_deserialize_5_b8(bytes);
    Eurydice_arr_e2 uu____1 =
        decompress_ciphertext_coefficient_b8_f4(re.data[i0]);
    re.data[i0] = uu____1;
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
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_ring_element_v_ff(Eurydice_slice serialized) {
  return deserialize_then_decompress_5_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.polynomial.subtract_reduce
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_b9
subtract_reduce_ea(Eurydice_arr_b9 *myself, Eurydice_arr_b9 b) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient_normal_form =
        libcrux_ml_kem_vector_portable_montgomery_multiply_by_constant_b8(
            b.data[i0], (int16_t)1441);
    Eurydice_arr_e2 diff = libcrux_ml_kem_vector_portable_sub_b8(
        myself->data[i0], &coefficient_normal_form);
    Eurydice_arr_e2 red =
        libcrux_ml_kem_vector_portable_barrett_reduce_b8(diff);
    b.data[i0] = red;
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
static KRML_MUSTINLINE Eurydice_arr_b9
subtract_reduce_d6_ea(Eurydice_arr_b9 *self, Eurydice_arr_b9 b) {
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
static KRML_MUSTINLINE Eurydice_arr_b9
compute_message_d0(Eurydice_arr_b9 *v, Eurydice_arr_0d *secret_as_ntt,
                   Eurydice_arr_0d *u_as_ntt) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
                  add_to_ring_element_d6_d0(&result, &product););
  invert_ntt_montgomery_d0(&result);
  return subtract_reduce_d6_ea(v, result);
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_message with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics

*/
static KRML_MUSTINLINE Eurydice_arr_60
compress_then_serialize_message_ea(Eurydice_arr_b9 re) {
  Eurydice_arr_60 serialized = {.data = {0U}};
  KRML_MAYBE_FOR16(
      i, (size_t)0U, (size_t)16U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_e2 coefficient = to_unsigned_field_modulus_ea(re.data[i0]);
      Eurydice_arr_e2 coefficient_compressed =
          libcrux_ml_kem_vector_portable_compress_1_b8(coefficient);
      Eurydice_arr_8b bytes =
          libcrux_ml_kem_vector_portable_serialize_1_b8(coefficient_compressed);
      Eurydice_slice_copy(
          Eurydice_array_to_subslice3(&serialized, (size_t)2U * i0,
                                      (size_t)2U * i0 + (size_t)2U, uint8_t *),
          Eurydice_array_to_slice((size_t)2U, &bytes, uint8_t), uint8_t););
  return serialized;
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_7d(Eurydice_arr_0d *secret_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_0d u_as_ntt = deserialize_then_decompress_u_00(ciphertext);
  Eurydice_arr_b9 v = deserialize_then_decompress_ring_element_v_ff(
      Eurydice_array_to_subslice_from((size_t)1568U, ciphertext, (size_t)1408U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_b9 message = compute_message_d0(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_ea(message);
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE Eurydice_arr_60 PRF_9e(Eurydice_slice input) {
  Eurydice_arr_60 digest = {.data = {0U}};
  libcrux_sha3_portable_shake256(
      Eurydice_array_to_slice((size_t)32U, &digest, uint8_t), input);
  return digest;
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
static KRML_MUSTINLINE Eurydice_arr_60 PRF_4a_44(Eurydice_slice input) {
  return PRF_9e(input);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_511(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair,
    Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_7d(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_e7 to_hash =
      libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_4a_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext = encrypt_unpacked_2a1(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
          Eurydice_array_to_slice((size_t)1568U, &expected_ciphertext,
                                  uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
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
static Eurydice_arr_b9 call_mut_0b_d0(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_0d
deserialize_ring_elements_reduced_out_d0(Eurydice_slice public_key) {
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_d0(&lvalue););
  Eurydice_arr_0d deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_d0(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_ff(
    Eurydice_arr_00 *public_key) {
  Eurydice_arr_0d deserialized_pk =
      deserialize_ring_elements_reduced_out_d0(Eurydice_array_to_subslice_to(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_0d *uu____0 = &deserialized_pk;
  Eurydice_arr_00 public_key_serialized = serialize_public_key_ff(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1568U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)1568U, public_key, &public_key_serialized,
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
    Eurydice_arr_17 *private_key) {
  Eurydice_arr_60 t = H_4a_ac(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)4U,
      (size_t)768U * (size_t)4U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)4U + (size_t)32U,
      (size_t)768U * (size_t)4U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *_ciphertext) {
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
  Eurydice_arr_0d private_key = default_70_d0();
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
static KRML_MUSTINLINE Eurydice_arr_17 serialize_kem_secret_key_60(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_17 out = {.data = {0U}};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_60(
      private_key, public_key, implicit_rejection_value, &out);
  return out;
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
libcrux_ml_kem_ind_cca_generate_keypair_151(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair1024 uu____0 =
      generate_keypair_ea1(ind_cpa_keypair_randomness);
  Eurydice_arr_38 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_00 public_key = uu____0.snd;
  Eurydice_arr_17 secret_key_serialized = serialize_kem_secret_key_60(
      Eurydice_array_to_slice((size_t)1536U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1568U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_17 private_key =
      libcrux_ml_kem_types_from_77_39(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_94(
      private_key, libcrux_ml_kem_types_from_fd_af(public_key));
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
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_03(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_00 encrypt_2a1(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_af
      unpacked_public_key = build_unpacked_public_key_3f1(public_key);
  return encrypt_unpacked_2a1(&unpacked_public_key, message, randomness);
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
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_60(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_2b libcrux_ml_kem_ind_cca_encapsulate_ca1(Eurydice_arr_00 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_03(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_ac(Eurydice_array_to_slice(
      (size_t)1568U, libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_ac(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_00 ciphertext =
      encrypt_2a1(Eurydice_array_to_slice(
                      (size_t)1568U,
                      libcrux_ml_kem_types_as_slice_e6_af(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_00 uu____2 = libcrux_ml_kem_types_from_e0_af(ciphertext);
  return (
      KRML_CLITERAL(tuple_2b){.fst = uu____2, .snd = kdf_39_60(shared_secret)});
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
static Eurydice_arr_b9 call_mut_0b_7d(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_7d(Eurydice_slice secret_key,
                                                  Eurydice_arr_00 *ciphertext) {
  Eurydice_arr_0d arr_struct;
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_7d(&lvalue););
  Eurydice_arr_0d secret_key_unpacked = arr_struct;
  deserialize_vector_d0(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_7d(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_621(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_1f(
          Eurydice_array_to_slice((size_t)3168U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_7d(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_ac(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_e7 to_hash =
      libcrux_ml_kem_utils_into_padded_array_7f(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1600U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_4a_44(Eurydice_array_to_slice((size_t)1600U, &to_hash, uint8_t));
  Eurydice_arr_00 expected_ciphertext =
      encrypt_2a1(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_60(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_60(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_af(ciphertext),
      Eurydice_array_to_slice((size_t)1568U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
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
    Eurydice_slice public_key, Eurydice_arr_270 *deserialized_pk) {
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
    Eurydice_arr_b9 uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_73
shake128_init_absorb_final_fd(Eurydice_arr_340 *input) {
  Eurydice_arr_73 shake128_state;
  Eurydice_arr_26 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.data, repeat_expression,
         (size_t)2U * sizeof(Eurydice_arr_26));
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.data[i0],
          Eurydice_array_to_slice((size_t)34U, &input->data[i0], uint8_t)););
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
Eurydice_arr_73
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
    Eurydice_arr_340 *input) {
  return shake128_init_absorb_final_fd(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_45
shake128_squeeze_first_three_blocks_fd(Eurydice_arr_73 *st) {
  Eurydice_arr_45 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)504U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_45
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
    Eurydice_arr_73 *self) {
  return shake128_squeeze_first_three_blocks_fd(self);
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
    Eurydice_arr_45 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_a9
shake128_squeeze_next_block_fd(Eurydice_arr_73 *st) {
  Eurydice_arr_a9 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)168U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_a9
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
    Eurydice_arr_73 *self) {
  return shake128_squeeze_next_block_fd(self);
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
    Eurydice_arr_a9 *randomness, Eurydice_arr_fb *sampled_coefficients,
    Eurydice_arr_04 *out) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static Eurydice_arr_b9 call_mut_e7_2b0(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE Eurydice_arr_270
sample_from_xof_2b0(Eurydice_arr_340 *seeds) {
  Eurydice_arr_fb sampled_coefficients = {.data = {0U}};
  Eurydice_arr_04 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_73 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_fd(
          seeds);
  Eurydice_arr_45 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_fd(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_64(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_a9 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_fd(
              &xof_state);
      done = sample_from_uniform_distribution_next_640(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_270 arr_mapped_str;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_2b0(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] with const
generics
- K= 2
*/
static KRML_MUSTINLINE void sample_matrix_A_2b0(Eurydice_arr_e20 *A_transpose,
                                                Eurydice_arr_480 *seed,
                                                bool transpose) {
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_340 seeds; Eurydice_arr_480 repeat_expression[2U];
      KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)2U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_270 sampled = sample_from_xof_2b0(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)2U, &sampled,
                                                          Eurydice_arr_b9),
                                  Eurydice_arr_b9);
           i++) {
        size_t j = i;
        Eurydice_arr_b9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
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
static KRML_MUSTINLINE Eurydice_arr_60 H_4a_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_H(input);
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
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_a0(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 =
      libcrux_ml_kem_utils_into_padded_array_9e(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_e20 *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue =
      libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_array_to_subslice_from(
          (size_t)800U, public_key, (size_t)768U, uint8_t, size_t, uint8_t[]));
  sample_matrix_A_2b0(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_4a_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
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
static KRML_MUSTINLINE void serialize_vector_a0(Eurydice_arr_270 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, key, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_ea(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_270 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_30 *serialized) {
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
    Eurydice_arr_30 *serialized) {
  serialize_public_key_mut_64(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
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
    Eurydice_arr_30 *serialized) {
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
static KRML_MUSTINLINE Eurydice_arr_30
serialize_public_key_64(Eurydice_arr_270 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_30 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_64(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
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
static KRML_MUSTINLINE Eurydice_arr_30 serialized_dd_64(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *self) {
  return libcrux_ml_kem_types_from_fd_4d(serialize_public_key_64(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
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
Eurydice_arr_30 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_64(
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
    Eurydice_arr_270 *private_key) {
  Eurydice_arr_30 public_key_serialized = serialize_public_key_64(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_56 secret_key_serialized = {.data = {0U}};
  serialize_vector_a0(
      private_key,
      Eurydice_array_to_slice((size_t)768U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair512){
      .fst = secret_key_serialized, .snd = public_key_serialized});
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_7f0 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_7f0 *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_7f0 *uu____3 = serialized;
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
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_fd(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_7f0 *uu____7 = serialized;
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
    Eurydice_arr_7f0 *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      serialize_unpacked_secret_key_86(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_56 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_30 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
      Eurydice_array_to_slice((size_t)768U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
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
Eurydice_arr_7f0 libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_6d(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *self) {
  Eurydice_arr_7f0 sk = libcrux_ml_kem_types_default_d3_2a();
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
    Eurydice_slice secret_key, Eurydice_arr_270 *secret_as_ntt) {
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
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
  deserialize_ring_elements_reduced_a0(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)768U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_e20 *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_2b0(uu____1, &lvalue, false);
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
    Eurydice_arr_7f0 *private_key,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_a0(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_3f0(ind_cpa_public_key,
                                    &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
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
static Eurydice_arr_270 default_70_a0(void) {
  Eurydice_arr_270 lit;
  Eurydice_arr_b9 repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_b9));
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
  Eurydice_arr_270 uu____0;
  Eurydice_arr_b9 repeat_expression0[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_ea(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)2U * sizeof(Eurydice_arr_b9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_270 repeat_expression1[2U];
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, Eurydice_arr_270 lit;
      Eurydice_arr_b9 repeat_expression[2U];
      KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(lit.data, repeat_expression, (size_t)2U * sizeof(Eurydice_arr_b9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1,
         (size_t)2U * sizeof(Eurydice_arr_270));
  return lit0;
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
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4){
      .ind_cpa_public_key = default_8b_a0(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
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
      .ind_cpa_private_key = default_70_a0(),
      .implicit_rejection_value = {.data = {0U}}};
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_4a_fd(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_G(input);
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_10(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)2U;
  return G_4a_fd(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 2
- LEN= 192
*/
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_49(Eurydice_arr_cf *input) {
  Eurydice_arr_a80 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_f2){
              .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_f2){
              .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                       0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)192U, &out.data[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, &input->data[i0], uint8_t)););
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_a80 PRFxN_4a_49(Eurydice_arr_cf *input) {
  return PRFxN_49(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- ETA= 3
*/
static KRML_MUSTINLINE Eurydice_arr_b9
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
    Eurydice_arr_270 *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_cf prf_inputs;
  Eurydice_arr_3e repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)2U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(&prf_inputs, domain_separator);
  Eurydice_arr_a80 prf_outputs = PRFxN_4a_49(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_1b(Eurydice_array_to_slice(
              (size_t)192U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt->data[i0]););
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
static Eurydice_arr_b9 call_mut_73_1c0(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE void add_to_ring_element_a0(Eurydice_arr_b9 *myself,
                                                   Eurydice_arr_b9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, Eurydice_arr_e2),
               Eurydice_arr_e2);
       i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
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
static KRML_MUSTINLINE void add_to_ring_element_d6_a0(Eurydice_arr_b9 *self,
                                                      Eurydice_arr_b9 *rhs) {
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
    Eurydice_arr_270 *t_as_ntt, Eurydice_arr_e20 *matrix_A,
    Eurydice_arr_270 *s_as_ntt, Eurydice_arr_270 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, matrix_A, Eurydice_arr_270),
               Eurydice_arr_270);
       i++) {
    size_t i0 = i;
    Eurydice_arr_270 *row = &matrix_A->data[i0];
    Eurydice_arr_b9 uu____0 = ZERO_d6_ea();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_b9),
                  Eurydice_arr_b9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_b9 *matrix_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_a0(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
    Eurydice_slice key_generation_seed, Eurydice_arr_270 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_10(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_e20 *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_2b0(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b0(private_key, &prf_input, 0U);
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_1c0(&lvalue););
  Eurydice_arr_270 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_3b0(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_a0(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
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
static Eurydice_arr_b9 call_mut_b4_a0(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_270 call_mut_7b_a0(void **_) {
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_a0(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static Eurydice_arr_e20 transpose_a_a0(Eurydice_arr_e20 ind_cpa_a) {
  Eurydice_arr_e20 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_a0(&lvalue););
  Eurydice_arr_e20 A = arr_struct;
  KRML_MAYBE_FOR2(
      i0, (size_t)0U, (size_t)2U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR2(
          i, (size_t)0U, (size_t)2U, (size_t)1U, size_t j = i;
          Eurydice_arr_b9 uu____0 = clone_c1_ea(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
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
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c0(ind_cpa_keypair_randomness,
                                &out->private_key.ind_cpa_private_key,
                                &out->public_key.ind_cpa_public_key);
  Eurydice_arr_e20 A = transpose_a_a0(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_30 pk_serialized = serialize_public_key_64(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_4a_fd(Eurydice_array_to_slice((size_t)800U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]]
with const generics
- K= 2
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_10(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_4a_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[[$2size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_71_s {
  Eurydice_arr_270 fst;
  Eurydice_arr_b9 snd;
} tuple_71;

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
static Eurydice_arr_b9 call_mut_f1_850(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_b9 call_mut_dd_850(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 2
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_490(Eurydice_arr_cf *input) {
  Eurydice_arr_a01 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, &out.data[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, &input->data[i0], uint8_t)););
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_a01 PRFxN_4a_490(Eurydice_arr_cf *input) {
  return PRFxN_490(input);
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
    Eurydice_arr_3e *prf_input, uint8_t domain_separator,
    Eurydice_arr_270 *error_1) {
  Eurydice_arr_cf prf_inputs;
  Eurydice_arr_3e repeat_expression[2U];
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)2U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_fd(&prf_inputs, domain_separator);
  Eurydice_arr_a01 prf_outputs = PRFxN_4a_490(&prf_inputs);
  KRML_MAYBE_FOR2(
      i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          sample_from_binomial_distribution_a0(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
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
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_4a_490(Eurydice_slice input) {
  return PRF_a6(input);
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
static Eurydice_arr_b9 call_mut_a8_a0(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 2
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_a0(Eurydice_arr_b9 *re) {
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
static KRML_MUSTINLINE Eurydice_arr_270
compute_vector_u_a0(Eurydice_arr_e20 *a_as_ntt, Eurydice_arr_270 *r_as_ntt,
                    Eurydice_arr_270 *error_1) {
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_a0(&lvalue););
  Eurydice_arr_270 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)2U, a_as_ntt, Eurydice_arr_270),
                Eurydice_arr_270);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_270 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)2U, row, Eurydice_arr_b9),
                 Eurydice_arr_b9);
         i++) {
      size_t j = i;
      Eurydice_arr_b9 *a_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_a0(&result.data[i1], &product);
    }
    invert_ntt_montgomery_a0(&result.data[i1]);
    add_error_reduce_d6_ea(&result.data[i1], &error_1->data[i1]);
  }
  return result;
}

/**
A monomorphic instance of libcrux_ml_kem.serialize.compress_then_serialize_10
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_10_ff(Eurydice_arr_b9 *re) {
  Eurydice_arr_b7 serialized = {.data = {0U}};
  for (size_t i = (size_t)0U;
       i < LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    Eurydice_arr_e2 coefficient =
        compress_b8_ef(to_unsigned_field_modulus_ea(re->data[i0]));
    Eurydice_arr_dc bytes =
        libcrux_ml_kem_vector_portable_serialize_10_b8(coefficient);
    Eurydice_slice_copy(
        Eurydice_array_to_subslice3(&serialized, (size_t)20U * i0,
                                    (size_t)20U * i0 + (size_t)20U, uint8_t *),
        Eurydice_array_to_slice((size_t)20U, &bytes, uint8_t), uint8_t);
  }
  return serialized;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
- OUT_LEN= 320
*/
static KRML_MUSTINLINE Eurydice_arr_b7
compress_then_serialize_ring_element_u_fe(Eurydice_arr_b9 *re) {
  return compress_then_serialize_10_ff(re);
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
static KRML_MUSTINLINE void compress_then_serialize_u_6d(Eurydice_arr_270 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)2U, &input, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)640U / (size_t)2U),
        (i0 + (size_t)1U) * ((size_t)640U / (size_t)2U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_fe(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_71 encrypt_c1_850(Eurydice_slice randomness,
                                               Eurydice_arr_e20 *matrix,
                                               Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_270 arr_struct0;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_850(&lvalue););
  Eurydice_arr_270 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b0(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_850(&lvalue););
  Eurydice_arr_270 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_3b0(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_4a_490(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_b9 error_2 = sample_from_binomial_distribution_a0(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_270 u = compute_vector_u_a0(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_6d(u, ciphertext);
  return (KRML_CLITERAL(tuple_71){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_b9 compute_ring_element_v_a0(
    Eurydice_arr_270 *t_as_ntt, Eurydice_arr_270 *r_as_ntt,
    Eurydice_arr_b9 *error_2, Eurydice_arr_b9 *message) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
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
    Eurydice_arr_b9 re, Eurydice_slice out) {
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
static KRML_MUSTINLINE void encrypt_c2_86(Eurydice_arr_270 *t_as_ntt,
                                          Eurydice_arr_270 *r_as_ntt,
                                          Eurydice_arr_b9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_b9 message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  Eurydice_arr_b9 v = compute_ring_element_v_a0(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_unpacked_2a0(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_56 ciphertext = {.data = {0U}};
  tuple_71 uu____0 =
      encrypt_c1_850(randomness, &public_key->A,
                     Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                 (size_t)640U, uint8_t *));
  Eurydice_arr_270 r_as_ntt = uu____0.fst;
  Eurydice_arr_b9 error_2 = uu____0.snd;
  Eurydice_arr_270 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_270 *uu____2 = &r_as_ntt;
  Eurydice_arr_b9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_86(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)768U, &ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
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
tuple_17 libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_10(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_56 ciphertext = encrypt_unpacked_2a0(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_17){
      .fst = libcrux_ml_kem_types_from_e0_d0(ciphertext),
      .snd = shared_secret_array});
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
static Eurydice_arr_b9 call_mut_35_86(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_u with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE Eurydice_arr_b9
deserialize_then_decompress_ring_element_u_0a(Eurydice_slice serialized) {
  return deserialize_then_decompress_10_ea(serialized);
}

/**
A monomorphic instance of libcrux_ml_kem.ntt.ntt_vector_u
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_0a(Eurydice_arr_b9 *re) {
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
static KRML_MUSTINLINE Eurydice_arr_270
deserialize_then_decompress_u_86(Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_86(&lvalue););
  Eurydice_arr_270 u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_0a(u_bytes);
    ntt_vector_u_0a(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 2
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_b9
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
static KRML_MUSTINLINE Eurydice_arr_b9
compute_message_a0(Eurydice_arr_b9 *v, Eurydice_arr_270 *secret_as_ntt,
                   Eurydice_arr_270 *u_as_ntt) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_d1(Eurydice_arr_270 *secret_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_270 u_as_ntt = deserialize_then_decompress_u_86(ciphertext);
  Eurydice_arr_b9 v = deserialize_then_decompress_ring_element_v_64(
      Eurydice_array_to_subslice_from((size_t)768U, ciphertext, (size_t)640U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_b9 message = compute_message_a0(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_ea(message);
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
static KRML_MUSTINLINE Eurydice_arr_60 PRF_4a_49(Eurydice_slice input) {
  return PRF_9e(input);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_510(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_d1(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_30 to_hash =
      libcrux_ml_kem_utils_into_padded_array_4d(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_4a_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext = encrypt_unpacked_2a0(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
          Eurydice_array_to_slice((size_t)768U, &expected_ciphertext, uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
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
static Eurydice_arr_b9 call_mut_0b_a0(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_270
deserialize_ring_elements_reduced_out_a0(Eurydice_slice public_key) {
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_a0(&lvalue););
  Eurydice_arr_270 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_a0(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_64(
    Eurydice_arr_30 *public_key) {
  Eurydice_arr_270 deserialized_pk =
      deserialize_ring_elements_reduced_out_a0(Eurydice_array_to_subslice_to(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_270 *uu____0 = &deserialized_pk;
  Eurydice_arr_30 public_key_serialized = serialize_public_key_64(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)800U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)2U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)800U, public_key, &public_key_serialized,
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
    Eurydice_arr_7f0 *private_key) {
  Eurydice_arr_60 t = H_4a_fd(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)2U,
      (size_t)768U * (size_t)2U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)2U + (size_t)32U,
      (size_t)768U * (size_t)2U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *_ciphertext) {
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
  Eurydice_arr_270 private_key = default_70_a0();
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
static KRML_MUSTINLINE Eurydice_arr_7f0 serialize_kem_secret_key_30(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_7f0 out = {.data = {0U}};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_30(
      private_key, public_key, implicit_rejection_value, &out);
  return out;
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
libcrux_ml_kem_ind_cca_generate_keypair_150(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair512 uu____0 =
      generate_keypair_ea0(ind_cpa_keypair_randomness);
  Eurydice_arr_56 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_30 public_key = uu____0.snd;
  Eurydice_arr_7f0 secret_key_serialized = serialize_kem_secret_key_30(
      Eurydice_array_to_slice((size_t)768U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)800U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_7f0 private_key =
      libcrux_ml_kem_types_from_77_2a(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_fa(
      private_key, libcrux_ml_kem_types_from_fd_4d(public_key));
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
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_10(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_56 encrypt_2a0(Eurydice_slice public_key,
                                                   Eurydice_arr_60 *message,
                                                   Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_d4
      unpacked_public_key = build_unpacked_public_key_3f0(public_key);
  return encrypt_unpacked_2a0(&unpacked_public_key, message, randomness);
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
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_30(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_17 libcrux_ml_kem_ind_cca_encapsulate_ca0(Eurydice_arr_30 *public_key,
                                                Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_10(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_fd(Eurydice_array_to_slice(
      (size_t)800U, libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_fd(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_56 ciphertext =
      encrypt_2a0(Eurydice_array_to_slice(
                      (size_t)800U,
                      libcrux_ml_kem_types_as_slice_e6_4d(public_key), uint8_t),
                  &randomness0, pseudorandomness);
  Eurydice_arr_56 uu____2 = libcrux_ml_kem_types_from_e0_d0(ciphertext);
  return (
      KRML_CLITERAL(tuple_17){.fst = uu____2, .snd = kdf_39_30(shared_secret)});
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
static Eurydice_arr_b9 call_mut_0b_d1(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_d1(Eurydice_slice secret_key,
                                                  Eurydice_arr_56 *ciphertext) {
  Eurydice_arr_270 arr_struct;
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_d1(&lvalue););
  Eurydice_arr_270 secret_key_unpacked = arr_struct;
  deserialize_vector_a0(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_d1(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_620(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_0c(
          Eurydice_array_to_slice((size_t)1632U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_d1(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_fd(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_30 to_hash =
      libcrux_ml_kem_utils_into_padded_array_4d(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)800U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_4a_49(Eurydice_array_to_slice((size_t)800U, &to_hash, uint8_t));
  Eurydice_arr_56 expected_ciphertext =
      encrypt_2a0(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_30(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_30(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_d0(ciphertext),
      Eurydice_array_to_slice((size_t)768U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
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
    Eurydice_slice public_key, Eurydice_arr_c41 *deserialized_pk) {
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
    Eurydice_arr_b9 uu____0 =
        deserialize_to_reduced_ring_element_ea(ring_element);
    deserialized_pk->data[i0] = uu____0;
  }
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_init_absorb_final with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_e4
shake128_init_absorb_final_e0(Eurydice_arr_84 *input) {
  Eurydice_arr_e4 shake128_state;
  Eurydice_arr_26 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      libcrux_sha3_portable_incremental_shake128_init(););
  memcpy(shake128_state.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_26));
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_absorb_final(
          &shake128_state.data[i0],
          Eurydice_array_to_slice((size_t)34U, &input->data[i0], uint8_t)););
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
Eurydice_arr_e4
libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
    Eurydice_arr_84 *input) {
  return shake128_init_absorb_final_e0(input);
}

/**
A monomorphic instance of
libcrux_ml_kem.hash_functions.portable.shake128_squeeze_first_three_blocks with
const generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_35
shake128_squeeze_first_three_blocks_e0(Eurydice_arr_e4 *st) {
  Eurydice_arr_35 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data =
                  {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
          (KRML_CLITERAL(Eurydice_arr_b0){
              .data = {
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                  0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)504U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_35
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
    Eurydice_arr_e4 *self) {
  return shake128_squeeze_first_three_blocks_e0(self);
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
    Eurydice_arr_35 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static KRML_MUSTINLINE Eurydice_arr_d6
shake128_squeeze_next_block_e0(Eurydice_arr_e4 *st) {
  Eurydice_arr_d6 out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_27){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_incremental_shake128_squeeze_next_block(
          &st->data[i0],
          Eurydice_array_to_slice((size_t)168U, &out.data[i0], uint8_t)););
  return out;
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
Eurydice_arr_d6
libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
    Eurydice_arr_e4 *self) {
  return shake128_squeeze_next_block_e0(self);
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
    Eurydice_arr_d6 *randomness, Eurydice_arr_c8 *sampled_coefficients,
    Eurydice_arr_d4 *out) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
        size_t r = i;
        if (sampled_coefficients->data[i1] <
            LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
          size_t sampled = libcrux_ml_kem_vector_portable_rej_sample_b8(
              Eurydice_array_to_subslice3(
                  &randomness->data[i1], r * (size_t)24U,
                  r * (size_t)24U + (size_t)24U, uint8_t *),
              Eurydice_array_to_subslice3(
                  &out->data[i1], sampled_coefficients->data[i1],
                  sampled_coefficients->data[i1] + (size_t)16U, int16_t *));
          size_t uu____0 = i1;
          sampled_coefficients->data[uu____0] =
              sampled_coefficients->data[uu____0] + sampled;
        }
      });
  bool done = true;
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      if (sampled_coefficients->data[i0] >=
          LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        sampled_coefficients->data[i0] =
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
static Eurydice_arr_b9 call_mut_e7_2b(Eurydice_arr_a00 tupled_args) {
  Eurydice_arr_a00 s = tupled_args;
  return from_i16_array_d6_ea(
      Eurydice_array_to_subslice3(&s, (size_t)0U, (size_t)256U, int16_t *));
}

/**
A monomorphic instance of libcrux_ml_kem.sampling.sample_from_xof
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE Eurydice_arr_c41
sample_from_xof_2b(Eurydice_arr_84 *seeds) {
  Eurydice_arr_c8 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_d4 out = {
      .data = {
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data =
                  {(int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                   (int16_t)0, (int16_t)0}}),
          (KRML_CLITERAL(Eurydice_arr_a00){
              .data = {
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0, (int16_t)0,
                  (int16_t)0, (int16_t)0}})}};
  Eurydice_arr_e4 xof_state =
      libcrux_ml_kem_hash_functions_portable_shake128_init_absorb_final_4a_e0(
          seeds);
  Eurydice_arr_35 randomness0 =
      libcrux_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_4a_e0(
          &xof_state);
  bool done = sample_from_uniform_distribution_next_89(
      &randomness0, &sampled_coefficients, &out);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_d6 randomness =
          libcrux_ml_kem_hash_functions_portable_shake128_squeeze_next_block_4a_e0(
              &xof_state);
      done = sample_from_uniform_distribution_next_890(
          &randomness, &sampled_coefficients, &out);
    }
  }
  Eurydice_arr_c41 arr_mapped_str;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  arr_mapped_str.data[i] = call_mut_e7_2b(out.data[i]););
  return arr_mapped_str;
}

/**
A monomorphic instance of libcrux_ml_kem.matrix.sample_matrix_A
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] with const
generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_2b(Eurydice_arr_aa *A_transpose,
                                               Eurydice_arr_480 *seed,
                                               bool transpose) {
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0;
      Eurydice_arr_84 seeds; Eurydice_arr_480 repeat_expression[3U];
      KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U,
          repeat_expression[i] =
              core_array__core__clone__Clone_for__Array_T__N___clone(
                  (size_t)34U, seed, uint8_t, Eurydice_arr_480););
      memcpy(seeds.data, repeat_expression,
             (size_t)3U * sizeof(Eurydice_arr_480));
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
                      seeds.data[j].data[32U] = (uint8_t)i1;
                      seeds.data[j].data[33U] = (uint8_t)j;);
      Eurydice_arr_c41 sampled = sample_from_xof_2b(&seeds);
      for (size_t i = (size_t)0U;
           i < Eurydice_slice_len(Eurydice_array_to_slice((size_t)3U, &sampled,
                                                          Eurydice_arr_b9),
                                  Eurydice_arr_b9);
           i++) {
        size_t j = i;
        Eurydice_arr_b9 sample = sampled.data[j];
        if (transpose) {
          A_transpose->data[j].data[i1] = sample;
        } else {
          A_transpose->data[i1].data[j] = sample;
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
static KRML_MUSTINLINE Eurydice_arr_60 H_4a_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_H(input);
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
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0
        *unpacked_public_key) {
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_to(
      (size_t)1184U, public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  deserialize_ring_elements_reduced_1b(
      uu____0, &unpacked_public_key->ind_cpa_public_key.t_as_ntt);
  Eurydice_arr_60 uu____1 = libcrux_ml_kem_utils_into_padded_array_9e(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  unpacked_public_key->ind_cpa_public_key.seed_for_A = uu____1;
  Eurydice_arr_aa *uu____2 = &unpacked_public_key->ind_cpa_public_key.A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(
      Eurydice_array_to_subslice_from((size_t)1184U, public_key, (size_t)1152U,
                                      uint8_t, size_t, uint8_t[]));
  sample_matrix_A_2b(uu____2, &lvalue, false);
  Eurydice_arr_60 uu____3 = H_4a_e0(Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t));
  unpacked_public_key->public_key_hash = uu____3;
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
  Eurydice_arr_c41 uu____0 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)3U, &self->t_as_ntt, Eurydice_arr_b9, Eurydice_arr_c41);
  Eurydice_arr_60 uu____1 =
      core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->seed_for_A, uint8_t, Eurydice_arr_60);
  return (
      KRML_CLITERAL(libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0){
          .t_as_ntt = uu____0,
          .seed_for_A = uu____1,
          .A = core_array__core__clone__Clone_for__Array_T__N___clone(
              (size_t)3U, &self->A, Eurydice_arr_c41, Eurydice_arr_aa)});
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
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 uu____0 =
      clone_91_1b(&self->ind_cpa_public_key);
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0){
      .ind_cpa_public_key = uu____0,
      .public_key_hash = core_array__core__clone__Clone_for__Array_T__N___clone(
          (size_t)32U, &self->public_key_hash, uint8_t, Eurydice_arr_60)});
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
static KRML_MUSTINLINE void serialize_vector_1b(Eurydice_arr_c41 *key,
                                                Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, key, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = key->data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        (i0 + (size_t)1U) * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
        uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_cc lvalue = serialize_uncompressed_ring_element_ea(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)384U, &lvalue, uint8_t),
                        uint8_t);
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
    Eurydice_arr_c41 *t_as_ntt, Eurydice_slice seed_for_a,
    Eurydice_arr_74 *serialized) {
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
    Eurydice_arr_74 *serialized) {
  serialize_public_key_mut_89(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t),
      serialized);
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
    Eurydice_arr_74 *serialized) {
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
static KRML_MUSTINLINE Eurydice_arr_74
serialize_public_key_89(Eurydice_arr_c41 *t_as_ntt, Eurydice_slice seed_for_a) {
  Eurydice_arr_74 public_key_serialized = {.data = {0U}};
  serialize_public_key_mut_89(t_as_ntt, seed_for_a, &public_key_serialized);
  return public_key_serialized;
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
static KRML_MUSTINLINE Eurydice_arr_74 serialized_dd_89(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *self) {
  return libcrux_ml_kem_types_from_fd_d0(serialize_public_key_89(
      &self->ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &self->ind_cpa_public_key.seed_for_A,
                              uint8_t)));
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
Eurydice_arr_74 libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_89(
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
    Eurydice_arr_c41 *private_key) {
  Eurydice_arr_74 public_key_serialized = serialize_public_key_89(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice((size_t)32U, &public_key->seed_for_A, uint8_t));
  Eurydice_arr_600 secret_key_serialized = {.data = {0U}};
  serialize_vector_1b(
      private_key,
      Eurydice_array_to_slice((size_t)1152U, &secret_key_serialized, uint8_t));
  return (KRML_CLITERAL(libcrux_ml_kem_utils_extraction_helper_Keypair768){
      .fst = secret_key_serialized, .snd = public_key_serialized});
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
    Eurydice_slice implicit_rejection_value, Eurydice_arr_ea *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_arr_ea *uu____0 = serialized;
  size_t uu____1 = pointer;
  size_t uu____2 = pointer;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          uu____0, uu____1, uu____2 + Eurydice_slice_len(private_key, uint8_t),
          uint8_t *),
      private_key, uint8_t);
  pointer = pointer + Eurydice_slice_len(private_key, uint8_t);
  Eurydice_arr_ea *uu____3 = serialized;
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
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_e0(public_key);
  Eurydice_slice_copy(
      uu____6, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  pointer = pointer + LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_arr_ea *uu____7 = serialized;
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
    Eurydice_arr_ea *serialized) {
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      serialize_unpacked_secret_key_6c(&self->public_key.ind_cpa_public_key,
                                       &self->private_key.ind_cpa_private_key);
  Eurydice_arr_600 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_74 ind_cpa_public_key = uu____0.snd;
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      Eurydice_array_to_slice((size_t)1152U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, &ind_cpa_public_key, uint8_t),
      Eurydice_array_to_slice(
          (size_t)32U, &self->private_key.implicit_rejection_value, uint8_t),
      serialized);
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
Eurydice_arr_ea libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_43(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *self) {
  Eurydice_arr_ea sk = libcrux_ml_kem_types_default_d3_28();
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
    Eurydice_slice secret_key, Eurydice_arr_c41 *secret_as_ntt) {
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          deserialize_to_uncompressed_ring_element_ea(Eurydice_slice_subslice3(
              secret_key, i0 * LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              (i0 + (size_t)1U) *
                  LIBCRUX_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
              uint8_t *));
      secret_as_ntt->data[i0] = uu____0;);
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
  deserialize_ring_elements_reduced_1b(uu____0, &unpacked_public_key->t_as_ntt);
  Eurydice_slice seed = Eurydice_slice_subslice_from(
      public_key, (size_t)1152U, uint8_t, size_t, uint8_t[]);
  Eurydice_arr_aa *uu____1 = &unpacked_public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue = libcrux_ml_kem_utils_into_padded_array_b6(seed);
  sample_matrix_A_2b(uu____1, &lvalue, false);
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
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked
        *key_pair) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  deserialize_vector_1b(ind_cpa_secret_key,
                        &key_pair->private_key.ind_cpa_private_key);
  build_unpacked_public_key_mut_3f(ind_cpa_public_key,
                                   &key_pair->public_key.ind_cpa_public_key);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      ind_cpa_public_key_hash, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->private_key.implicit_rejection_value,
                              uint8_t),
      implicit_rejection_value, uint8_t);
  Eurydice_slice_copy(
      Eurydice_array_to_slice(
          (size_t)32U, &key_pair->public_key.ind_cpa_public_key.seed_for_A,
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
static Eurydice_arr_c41 default_70_1b(void) {
  Eurydice_arr_c41 lit;
  Eurydice_arr_b9 repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] = ZERO_d6_ea(););
  memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_b9));
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
  Eurydice_arr_c41 uu____0;
  Eurydice_arr_b9 repeat_expression0[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression0[i] = ZERO_d6_ea(););
  memcpy(uu____0.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_b9));
  Eurydice_arr_60 uu____1 = {.data = {0U}};
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 lit0;
  lit0.t_as_ntt = uu____0;
  lit0.seed_for_A = uu____1;
  Eurydice_arr_c41 repeat_expression1[3U];
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, Eurydice_arr_c41 lit;
      Eurydice_arr_b9 repeat_expression[3U];
      KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                      repeat_expression[i] = ZERO_d6_ea(););
      memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_b9));
      repeat_expression1[i0] = lit;);
  memcpy(lit0.A.data, repeat_expression1,
         (size_t)3U * sizeof(Eurydice_arr_c41));
  return lit0;
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
  return (KRML_CLITERAL(
      libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0){
      .ind_cpa_public_key = default_8b_1b(),
      .public_key_hash = {.data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                                   0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}});
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
      .ind_cpa_private_key = default_70_1b(),
      .implicit_rejection_value = {.data = {0U}}};
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
G_4a_e0(Eurydice_slice input) {
  return libcrux_ml_kem_hash_functions_portable_G(input);
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
static KRML_MUSTINLINE libcrux_sha3_Sha3_512Digest
cpa_keygen_seed_39_9c(Eurydice_slice key_generation_seed) {
  Eurydice_arr_3e seed = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice3(
          &seed, (size_t)0U,
          LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      (uint8_t)(size_t)3U;
  return G_4a_e0(Eurydice_array_to_slice((size_t)33U, &seed, uint8_t));
}

/**
A monomorphic instance of libcrux_ml_kem.hash_functions.portable.PRFxN
with const generics
- K= 3
- LEN= 128
*/
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_41(Eurydice_arr_46 *input) {
  Eurydice_arr_db out = {
      .data = {(KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}}),
               (KRML_CLITERAL(Eurydice_arr_d1){
                   .data = {0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U,
                            0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})}};
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      libcrux_sha3_portable_shake256(
          Eurydice_array_to_slice((size_t)128U, &out.data[i0], uint8_t),
          Eurydice_array_to_slice((size_t)33U, &input->data[i0], uint8_t)););
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_db PRFxN_4a_41(Eurydice_arr_46 *input) {
  return PRFxN_41(input);
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
    Eurydice_arr_c41 *re_as_ntt, Eurydice_arr_3e *prf_input,
    uint8_t domain_separator) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_db prf_outputs = PRFxN_4a_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      re_as_ntt->data[i0] =
          sample_from_binomial_distribution_a0(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      ntt_binomially_sampled_ring_element_ea(&re_as_ntt->data[i0]););
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
static Eurydice_arr_b9 call_mut_73_1c(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE void add_to_ring_element_1b(Eurydice_arr_b9 *myself,
                                                   Eurydice_arr_b9 *rhs) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)16U, myself, Eurydice_arr_e2),
               Eurydice_arr_e2);
       i++) {
    size_t i0 = i;
    Eurydice_arr_e2 uu____0 =
        libcrux_ml_kem_vector_portable_add_b8(myself->data[i0], &rhs->data[i0]);
    myself->data[i0] = uu____0;
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
static KRML_MUSTINLINE void add_to_ring_element_d6_1b(Eurydice_arr_b9 *self,
                                                      Eurydice_arr_b9 *rhs) {
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
    Eurydice_arr_c41 *t_as_ntt, Eurydice_arr_aa *matrix_A,
    Eurydice_arr_c41 *s_as_ntt, Eurydice_arr_c41 *error_as_ntt) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, matrix_A, Eurydice_arr_c41),
               Eurydice_arr_c41);
       i++) {
    size_t i0 = i;
    Eurydice_arr_c41 *row = &matrix_A->data[i0];
    Eurydice_arr_b9 uu____0 = ZERO_d6_ea();
    t_as_ntt->data[i0] = uu____0;
    for (size_t i1 = (size_t)0U;
         i1 < Eurydice_slice_len(
                  Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_b9),
                  Eurydice_arr_b9);
         i1++) {
      size_t j = i1;
      Eurydice_arr_b9 *matrix_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(matrix_element, &s_as_ntt->data[j]);
      add_to_ring_element_d6_1b(&t_as_ntt->data[i0], &product);
    }
    add_standard_error_reduce_d6_ea(&t_as_ntt->data[i0],
                                    &error_as_ntt->data[i0]);
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
    Eurydice_slice key_generation_seed, Eurydice_arr_c41 *private_key,
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key) {
  libcrux_sha3_Sha3_512Digest hashed =
      cpa_keygen_seed_39_9c(key_generation_seed);
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t), (size_t)32U,
      uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice seed_for_A = uu____0.fst;
  Eurydice_slice seed_for_secret_and_error = uu____0.snd;
  Eurydice_arr_aa *uu____1 = &public_key->A;
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_480 lvalue0 =
      libcrux_ml_kem_utils_into_padded_array_b6(seed_for_A);
  sample_matrix_A_2b(uu____1, &lvalue0, true);
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(seed_for_secret_and_error);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_3b(private_key, &prf_input, 0U);
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_73_1c(&lvalue););
  Eurydice_arr_c41 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_3b(&error_as_ntt, &prf_input, domain_separator);
  compute_As_plus_e_1b(&public_key->t_as_ntt, &public_key->A, private_key,
                       &error_as_ntt);
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, seed_for_A, Eurydice_slice, Eurydice_arr_60,
                           core_array_TryFromSliceError);
  Eurydice_arr_60 uu____2 = core_result_unwrap_26_07(dst);
  public_key->seed_for_A = uu____2;
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
static Eurydice_arr_b9 call_mut_b4_1b(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_c41 call_mut_7b_1b(void **_) {
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_b4_1b(&lvalue););
  return arr_struct;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.transpose_a
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static Eurydice_arr_aa transpose_a_1b(Eurydice_arr_aa ind_cpa_a) {
  Eurydice_arr_aa arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_7b_1b(&lvalue););
  Eurydice_arr_aa A = arr_struct;
  KRML_MAYBE_FOR3(
      i0, (size_t)0U, (size_t)3U, (size_t)1U, size_t i1 = i0; KRML_MAYBE_FOR3(
          i, (size_t)0U, (size_t)3U, (size_t)1U, size_t j = i;
          Eurydice_arr_b9 uu____0 = clone_c1_ea(&ind_cpa_a.data[j].data[i1]);
          A.data[i1].data[j] = uu____0;););
  return A;
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
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *out) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      &randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, &randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  generate_keypair_unpacked_1c(ind_cpa_keypair_randomness,
                               &out->private_key.ind_cpa_private_key,
                               &out->public_key.ind_cpa_public_key);
  Eurydice_arr_aa A = transpose_a_1b(out->public_key.ind_cpa_public_key.A);
  out->public_key.ind_cpa_public_key.A = A;
  Eurydice_arr_74 pk_serialized = serialize_public_key_89(
      &out->public_key.ind_cpa_public_key.t_as_ntt,
      Eurydice_array_to_slice((size_t)32U,
                              &out->public_key.ind_cpa_public_key.seed_for_A,
                              uint8_t));
  out->public_key.public_key_hash =
      H_4a_e0(Eurydice_array_to_slice((size_t)1184U, &pk_serialized, uint8_t));
  core_result_Result_95 dst;
  Eurydice_slice_to_array2(&dst, implicit_rejection_value, Eurydice_slice,
                           Eurydice_arr_60, core_array_TryFromSliceError);
  Eurydice_arr_60 uu____1 = core_result_unwrap_26_07(dst);
  out->private_key.implicit_rejection_value = uu____1;
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encaps_prepare
with types libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]]
with const generics
- K= 3
*/
static libcrux_sha3_Sha3_512Digest encaps_prepare_9c(Eurydice_slice randomness,
                                                     Eurydice_slice pk_hash) {
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(randomness);
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from((size_t)64U, &to_hash,
                                      LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE,
                                      uint8_t, size_t, uint8_t[]),
      pk_hash, uint8_t);
  return G_4a_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
}

/**
A monomorphic instance of K.
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector[[$3size_t]],
libcrux_ml_kem_polynomial_PolynomialRingElement
libcrux_ml_kem_vector_portable_vector_type_PortableVector

*/
typedef struct tuple_88_s {
  Eurydice_arr_c41 fst;
  Eurydice_arr_b9 snd;
} tuple_88;

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
static Eurydice_arr_b9 call_mut_f1_85(void **_) { return ZERO_d6_ea(); }

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
static Eurydice_arr_b9 call_mut_dd_85(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE uint8_t
sample_ring_element_cbd_3b(Eurydice_arr_3e *prf_input, uint8_t domain_separator,
                           Eurydice_arr_c41 *error_1) {
  Eurydice_arr_46 prf_inputs;
  Eurydice_arr_3e repeat_expression[3U];
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  repeat_expression[i] =
                      core_array__core__clone__Clone_for__Array_T__N___clone(
                          (size_t)33U, prf_input, uint8_t, Eurydice_arr_3e););
  memcpy(prf_inputs.data, repeat_expression,
         (size_t)3U * sizeof(Eurydice_arr_3e));
  domain_separator =
      libcrux_ml_kem_utils_prf_input_inc_e0(&prf_inputs, domain_separator);
  Eurydice_arr_db prf_outputs = PRFxN_4a_41(&prf_inputs);
  KRML_MAYBE_FOR3(
      i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
      Eurydice_arr_b9 uu____0 =
          sample_from_binomial_distribution_a0(Eurydice_array_to_slice(
              (size_t)128U, &prf_outputs.data[i0], uint8_t));
      error_1->data[i0] = uu____0;);
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
static KRML_MUSTINLINE Eurydice_arr_d1 PRF_4a_410(Eurydice_slice input) {
  return PRF_a6(input);
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
static Eurydice_arr_b9 call_mut_a8_1b(void **_) { return ZERO_d6_ea(); }

/**
A monomorphic instance of libcrux_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_1b(Eurydice_arr_b9 *re) {
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
static KRML_MUSTINLINE Eurydice_arr_c41
compute_vector_u_1b(Eurydice_arr_aa *a_as_ntt, Eurydice_arr_c41 *r_as_ntt,
                    Eurydice_arr_c41 *error_1) {
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_a8_1b(&lvalue););
  Eurydice_arr_c41 result = arr_struct;
  for (size_t i0 = (size_t)0U;
       i0 < Eurydice_slice_len(
                Eurydice_array_to_slice((size_t)3U, a_as_ntt, Eurydice_arr_c41),
                Eurydice_arr_c41);
       i0++) {
    size_t i1 = i0;
    Eurydice_arr_c41 *row = &a_as_ntt->data[i1];
    for (size_t i = (size_t)0U;
         i < Eurydice_slice_len(
                 Eurydice_array_to_slice((size_t)3U, row, Eurydice_arr_b9),
                 Eurydice_arr_b9);
         i++) {
      size_t j = i;
      Eurydice_arr_b9 *a_element = &row->data[j];
      Eurydice_arr_b9 product =
          ntt_multiply_d6_ea(a_element, &r_as_ntt->data[j]);
      add_to_ring_element_d6_1b(&result.data[i1], &product);
    }
    invert_ntt_montgomery_1b(&result.data[i1]);
    add_error_reduce_d6_ea(&result.data[i1], &error_1->data[i1]);
  }
  return result;
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
static KRML_MUSTINLINE void compress_then_serialize_u_43(Eurydice_arr_c41 input,
                                                         Eurydice_slice out) {
  for (size_t i = (size_t)0U;
       i < Eurydice_slice_len(
               Eurydice_array_to_slice((size_t)3U, &input, Eurydice_arr_b9),
               Eurydice_arr_b9);
       i++) {
    size_t i0 = i;
    Eurydice_arr_b9 re = input.data[i0];
    Eurydice_slice uu____0 = Eurydice_slice_subslice3(
        out, i0 * ((size_t)960U / (size_t)3U),
        (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U), uint8_t *);
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_b7 lvalue = compress_then_serialize_ring_element_u_fe(&re);
    Eurydice_slice_copy(uu____0,
                        Eurydice_array_to_slice((size_t)320U, &lvalue, uint8_t),
                        uint8_t);
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
static KRML_MUSTINLINE tuple_88 encrypt_c1_85(Eurydice_slice randomness,
                                              Eurydice_arr_aa *matrix,
                                              Eurydice_slice ciphertext) {
  Eurydice_arr_3e prf_input =
      libcrux_ml_kem_utils_into_padded_array_c8(randomness);
  Eurydice_arr_c41 arr_struct0;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct0.data[i] = call_mut_f1_85(&lvalue););
  Eurydice_arr_c41 r_as_ntt = arr_struct0;
  uint8_t domain_separator0 =
      sample_vector_cbd_then_ntt_3b(&r_as_ntt, &prf_input, 0U);
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_dd_85(&lvalue););
  Eurydice_arr_c41 error_1 = arr_struct;
  uint8_t domain_separator =
      sample_ring_element_cbd_3b(&prf_input, domain_separator0, &error_1);
  prf_input.data[32U] = domain_separator;
  Eurydice_arr_d1 prf_output =
      PRF_4a_410(Eurydice_array_to_slice((size_t)33U, &prf_input, uint8_t));
  Eurydice_arr_b9 error_2 = sample_from_binomial_distribution_a0(
      Eurydice_array_to_slice((size_t)128U, &prf_output, uint8_t));
  Eurydice_arr_c41 u = compute_vector_u_1b(matrix, &r_as_ntt, &error_1);
  compress_then_serialize_u_43(u, ciphertext);
  return (KRML_CLITERAL(tuple_88){.fst = r_as_ntt, .snd = error_2});
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
static KRML_MUSTINLINE Eurydice_arr_b9 compute_ring_element_v_1b(
    Eurydice_arr_c41 *t_as_ntt, Eurydice_arr_c41 *r_as_ntt,
    Eurydice_arr_b9 *error_2, Eurydice_arr_b9 *message) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &t_as_ntt->data[i0], &r_as_ntt->data[i0]);
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
    Eurydice_arr_b9 re, Eurydice_slice out) {
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
static KRML_MUSTINLINE void encrypt_c2_6c(Eurydice_arr_c41 *t_as_ntt,
                                          Eurydice_arr_c41 *r_as_ntt,
                                          Eurydice_arr_b9 *error_2,
                                          Eurydice_arr_60 *message,
                                          Eurydice_slice ciphertext) {
  Eurydice_arr_b9 message_as_ring_element =
      deserialize_then_decompress_message_ea(message);
  Eurydice_arr_b9 v = compute_ring_element_v_1b(t_as_ntt, r_as_ntt, error_2,
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_unpacked_2a(
    libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0 *public_key,
    Eurydice_arr_60 *message, Eurydice_slice randomness) {
  Eurydice_arr_2c ciphertext = {.data = {0U}};
  tuple_88 uu____0 =
      encrypt_c1_85(randomness, &public_key->A,
                    Eurydice_array_to_subslice3(&ciphertext, (size_t)0U,
                                                (size_t)960U, uint8_t *));
  Eurydice_arr_c41 r_as_ntt = uu____0.fst;
  Eurydice_arr_b9 error_2 = uu____0.snd;
  Eurydice_arr_c41 *uu____1 = &public_key->t_as_ntt;
  Eurydice_arr_c41 *uu____2 = &r_as_ntt;
  Eurydice_arr_b9 *uu____3 = &error_2;
  Eurydice_arr_60 *uu____4 = message;
  encrypt_c2_6c(
      uu____1, uu____2, uu____3, uu____4,
      Eurydice_array_to_subslice_from((size_t)1088U, &ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  return ciphertext;
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
tuple_56 libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    Eurydice_arr_60 *randomness) {
  libcrux_sha3_Sha3_512Digest hashed = encaps_prepare_9c(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &public_key->public_key_hash,
                              uint8_t));
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____0.fst;
  Eurydice_slice pseudorandomness = uu____0.snd;
  Eurydice_arr_2c ciphertext = encrypt_unpacked_2a(
      &public_key->ind_cpa_public_key, randomness, pseudorandomness);
  Eurydice_arr_60 shared_secret_array = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_slice((size_t)32U, &shared_secret_array, uint8_t),
      shared_secret, uint8_t);
  return (KRML_CLITERAL(tuple_56){
      .fst = libcrux_ml_kem_types_from_e0_80(ciphertext),
      .snd = shared_secret_array});
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
static Eurydice_arr_b9 call_mut_35_6c(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_c41
deserialize_then_decompress_u_6c(Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_35_6c(&lvalue););
  Eurydice_arr_c41 u_as_ntt = arr_struct;
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
    u_as_ntt.data[i0] = deserialize_then_decompress_ring_element_u_0a(u_bytes);
    ntt_vector_u_0a(&u_as_ntt.data[i0]);
  }
  return u_as_ntt;
}

/**
A monomorphic instance of
libcrux_ml_kem.serialize.deserialize_then_decompress_ring_element_v with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector with const generics
- K= 3
- COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE Eurydice_arr_b9
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
static KRML_MUSTINLINE Eurydice_arr_b9
compute_message_1b(Eurydice_arr_b9 *v, Eurydice_arr_c41 *secret_as_ntt,
                   Eurydice_arr_c41 *u_as_ntt) {
  Eurydice_arr_b9 result = ZERO_d6_ea();
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  Eurydice_arr_b9 product = ntt_multiply_d6_ea(
                      &secret_as_ntt->data[i0], &u_as_ntt->data[i0]);
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
static KRML_MUSTINLINE Eurydice_arr_60
decrypt_unpacked_42(Eurydice_arr_c41 *secret_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_c41 u_as_ntt = deserialize_then_decompress_u_6c(ciphertext);
  Eurydice_arr_b9 v = deserialize_then_decompress_ring_element_v_89(
      Eurydice_array_to_subslice_from((size_t)1088U, ciphertext, (size_t)960U,
                                      uint8_t, size_t, uint8_t[]));
  Eurydice_arr_b9 message = compute_message_1b(&v, secret_key, &u_as_ntt);
  return compress_then_serialize_message_ea(message);
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
static KRML_MUSTINLINE Eurydice_arr_60 PRF_4a_41(Eurydice_slice input) {
  return PRF_9e(input);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_unpacked_decapsulate_51(
    libcrux_ml_kem_mlkem768_portable_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_60 decrypted = decrypt_unpacked_42(
      &key_pair->private_key.ind_cpa_private_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice((size_t)32U,
                              &key_pair->public_key.public_key_hash, uint8_t),
      uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_48 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(Eurydice_array_to_slice(
          (size_t)32U, &key_pair->private_key.implicit_rejection_value,
          uint8_t));
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      PRF_4a_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext = encrypt_unpacked_2a(
      &key_pair->public_key.ind_cpa_public_key, &decrypted, pseudorandomness);
  uint8_t selector =
      libcrux_ml_kem_constant_time_ops_compare_ciphertexts_in_constant_time(
          libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
          Eurydice_array_to_slice((size_t)1088U, &expected_ciphertext,
                                  uint8_t));
  return libcrux_ml_kem_constant_time_ops_select_shared_secret_in_constant_time(
      shared_secret,
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t),
      selector);
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
static Eurydice_arr_b9 call_mut_0b_1b(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_c41
deserialize_ring_elements_reduced_out_1b(Eurydice_slice public_key) {
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_1b(&lvalue););
  Eurydice_arr_c41 deserialized_pk = arr_struct;
  deserialize_ring_elements_reduced_1b(public_key, &deserialized_pk);
  return deserialized_pk;
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
bool libcrux_ml_kem_ind_cca_validate_public_key_89(
    Eurydice_arr_74 *public_key) {
  Eurydice_arr_c41 deserialized_pk =
      deserialize_ring_elements_reduced_out_1b(Eurydice_array_to_subslice_to(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]));
  Eurydice_arr_c41 *uu____0 = &deserialized_pk;
  Eurydice_arr_74 public_key_serialized = serialize_public_key_89(
      uu____0,
      Eurydice_array_to_subslice_from(
          (size_t)1184U, public_key,
          libcrux_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U),
          uint8_t, size_t, uint8_t[]));
  return Eurydice_array_eq((size_t)1184U, public_key, &public_key_serialized,
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
    Eurydice_arr_ea *private_key) {
  Eurydice_arr_60 t = H_4a_e0(Eurydice_array_to_subslice3(
      private_key, (size_t)384U * (size_t)3U,
      (size_t)768U * (size_t)3U + (size_t)32U, uint8_t *));
  Eurydice_slice expected = Eurydice_array_to_subslice3(
      private_key, (size_t)768U * (size_t)3U + (size_t)32U,
      (size_t)768U * (size_t)3U + (size_t)64U, uint8_t *);
  return Eurydice_array_eq_slice((size_t)32U, &t, &expected, uint8_t, bool);
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
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *_ciphertext) {
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
  Eurydice_arr_c41 private_key = default_70_1b();
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
static KRML_MUSTINLINE Eurydice_arr_ea serialize_kem_secret_key_d6(
    Eurydice_slice private_key, Eurydice_slice public_key,
    Eurydice_slice implicit_rejection_value) {
  Eurydice_arr_ea out = {.data = {0U}};
  libcrux_ml_kem_ind_cca_serialize_kem_secret_key_mut_d6(
      private_key, public_key, implicit_rejection_value, &out);
  return out;
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
libcrux_ml_kem_ind_cca_generate_keypair_15(
    libcrux_sha3_Sha3_512Digest *randomness) {
  Eurydice_slice ind_cpa_keypair_randomness = Eurydice_array_to_subslice3(
      randomness, (size_t)0U,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t *);
  Eurydice_slice implicit_rejection_value = Eurydice_array_to_subslice_from(
      (size_t)64U, randomness,
      LIBCRUX_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE, uint8_t,
      size_t, uint8_t[]);
  libcrux_ml_kem_utils_extraction_helper_Keypair768 uu____0 =
      generate_keypair_ea(ind_cpa_keypair_randomness);
  Eurydice_arr_600 ind_cpa_private_key = uu____0.fst;
  Eurydice_arr_74 public_key = uu____0.snd;
  Eurydice_arr_ea secret_key_serialized = serialize_kem_secret_key_d6(
      Eurydice_array_to_slice((size_t)1152U, &ind_cpa_private_key, uint8_t),
      Eurydice_array_to_slice((size_t)1184U, &public_key, uint8_t),
      implicit_rejection_value);
  Eurydice_arr_ea private_key =
      libcrux_ml_kem_types_from_77_28(secret_key_serialized);
  return libcrux_ml_kem_types_from_17_74(
      private_key, libcrux_ml_kem_types_from_fd_d0(public_key));
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
static KRML_MUSTINLINE Eurydice_arr_60
entropy_preprocess_39_9c(Eurydice_slice randomness) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      randomness, uint8_t);
  return out;
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
static KRML_MUSTINLINE Eurydice_arr_2c encrypt_2a(Eurydice_slice public_key,
                                                  Eurydice_arr_60 *message,
                                                  Eurydice_slice randomness) {
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_a0
      unpacked_public_key = build_unpacked_public_key_3f(public_key);
  return encrypt_unpacked_2a(&unpacked_public_key, message, randomness);
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
static KRML_MUSTINLINE Eurydice_arr_60 kdf_39_d6(Eurydice_slice shared_secret) {
  Eurydice_arr_60 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_slice((size_t)32U, &out, uint8_t),
                      shared_secret, uint8_t);
  return out;
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
tuple_56 libcrux_ml_kem_ind_cca_encapsulate_ca(Eurydice_arr_74 *public_key,
                                               Eurydice_arr_60 *randomness) {
  Eurydice_arr_60 randomness0 = entropy_preprocess_39_9c(
      Eurydice_array_to_slice((size_t)32U, randomness, uint8_t));
  libcrux_sha3_Sha3_512Digest to_hash =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &randomness0, uint8_t));
  Eurydice_slice uu____0 = Eurydice_array_to_subslice_from(
      (size_t)64U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      size_t, uint8_t[]);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_60 lvalue = H_4a_e0(Eurydice_array_to_slice(
      (size_t)1184U, libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t));
  Eurydice_slice_copy(
      uu____0, Eurydice_array_to_slice((size_t)32U, &lvalue, uint8_t), uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_e0(Eurydice_array_to_slice((size_t)64U, &to_hash, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_2c ciphertext =
      encrypt_2a(Eurydice_array_to_slice(
                     (size_t)1184U,
                     libcrux_ml_kem_types_as_slice_e6_d0(public_key), uint8_t),
                 &randomness0, pseudorandomness);
  Eurydice_arr_2c uu____2 = libcrux_ml_kem_types_from_e0_80(ciphertext);
  return (
      KRML_CLITERAL(tuple_56){.fst = uu____2, .snd = kdf_39_d6(shared_secret)});
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
static Eurydice_arr_b9 call_mut_0b_42(void **_) { return ZERO_d6_ea(); }

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
static KRML_MUSTINLINE Eurydice_arr_60 decrypt_42(Eurydice_slice secret_key,
                                                  Eurydice_arr_2c *ciphertext) {
  Eurydice_arr_c41 arr_struct;
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U,
                  /* original Rust expression is not an lvalue in C */
                  void *lvalue = (void *)0U;
                  arr_struct.data[i] = call_mut_0b_42(&lvalue););
  Eurydice_arr_c41 secret_key_unpacked = arr_struct;
  deserialize_vector_1b(secret_key, &secret_key_unpacked);
  return decrypt_unpacked_42(&secret_key_unpacked, ciphertext);
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
Eurydice_arr_60 libcrux_ml_kem_ind_cca_decapsulate_62(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  Eurydice_slice_uint8_t_x4 uu____0 =
      libcrux_ml_kem_types_unpack_private_key_b4(
          Eurydice_array_to_slice((size_t)2400U, private_key, uint8_t));
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice ind_cpa_public_key = uu____0.snd;
  Eurydice_slice ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_slice implicit_rejection_value = uu____0.f3;
  Eurydice_arr_60 decrypted = decrypt_42(ind_cpa_secret_key, ciphertext);
  libcrux_sha3_Sha3_512Digest to_hash0 =
      libcrux_ml_kem_utils_into_padded_array_24(
          Eurydice_array_to_slice((size_t)32U, &decrypted, uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from(
          (size_t)64U, &to_hash0, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
          uint8_t, size_t, uint8_t[]),
      ind_cpa_public_key_hash, uint8_t);
  libcrux_sha3_Sha3_512Digest hashed =
      G_4a_e0(Eurydice_array_to_slice((size_t)64U, &to_hash0, uint8_t));
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice((size_t)64U, &hashed, uint8_t),
      LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice shared_secret0 = uu____1.fst;
  Eurydice_slice pseudorandomness = uu____1.snd;
  Eurydice_arr_48 to_hash =
      libcrux_ml_kem_utils_into_padded_array_15(implicit_rejection_value);
  Eurydice_slice uu____2 = Eurydice_array_to_subslice_from(
      (size_t)1120U, &to_hash, LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
      uint8_t, size_t, uint8_t[]);
  Eurydice_slice_copy(uu____2, libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
                      uint8_t);
  Eurydice_arr_60 implicit_rejection_shared_secret0 =
      PRF_4a_41(Eurydice_array_to_slice((size_t)1120U, &to_hash, uint8_t));
  Eurydice_arr_2c expected_ciphertext =
      encrypt_2a(ind_cpa_public_key, &decrypted, pseudorandomness);
  Eurydice_arr_60 implicit_rejection_shared_secret =
      kdf_39_d6(Eurydice_array_to_slice(
          (size_t)32U, &implicit_rejection_shared_secret0, uint8_t));
  Eurydice_arr_60 shared_secret = kdf_39_d6(shared_secret0);
  return libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      libcrux_ml_kem_types_as_ref_d3_80(ciphertext),
      Eurydice_array_to_slice((size_t)1088U, &expected_ciphertext, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &shared_secret, uint8_t),
      Eurydice_array_to_slice((size_t)32U, &implicit_rejection_shared_secret,
                              uint8_t));
}
