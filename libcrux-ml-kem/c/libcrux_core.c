/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3275bf4ad9dc8c25965dc5da6122653fc43c4287
 * Eurydice: d3b14228e2b5fe8710ec7efae31e4de2c96ed20d
 * Karamel: 095cdb73f246711f93f99a159ceca37cd2c227e1
 * F*: 4b3fc11774003a6ff7c09500ecb5f0145ca6d862
 * Libcrux: 75cbe9ea0e459cf8a62d97e8a867411e0dd8529a
 */

#include "internal/libcrux_core.h"

/**
 Return 1 if `value` is not zero and 0 otherwise.
*/
static KRML_NOINLINE uint8_t inz(uint8_t value) {
  uint16_t value0 = (uint16_t)value;
  uint8_t result =
      (uint8_t)((uint32_t)core_num__u16_7__wrapping_add(~value0, 1U) >> 8U);
  return (uint32_t)result & 1U;
}

static KRML_NOINLINE uint8_t is_non_zero(uint8_t value) { return inz(value); }

/**
 Return 1 if the bytes of `lhs` and `rhs` do not exactly
 match and 0 otherwise.
*/
static KRML_NOINLINE uint8_t compare(Eurydice_slice lhs, Eurydice_slice rhs) {
  uint8_t r = 0U;
  for (size_t i = (size_t)0U; i < Eurydice_slice_len(lhs, uint8_t); i++) {
    size_t i0 = i;
    uint8_t nr = (uint32_t)r |
                 ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) ^
                  (uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *));
    r = nr;
  }
  return is_non_zero(r);
}

static KRML_NOINLINE uint8_t
compare_ciphertexts_in_constant_time(Eurydice_slice lhs, Eurydice_slice rhs) {
  return compare(lhs, rhs);
}

/**
 If `selector` is not zero, return the bytes in `rhs`; return the bytes in
 `lhs` otherwise.
*/
static KRML_NOINLINE void select_ct(Eurydice_slice lhs, Eurydice_slice rhs,
                                    uint8_t selector, uint8_t ret[32U]) {
  uint8_t mask = core_num__u8_6__wrapping_sub(is_non_zero(selector), 1U);
  uint8_t out[32U] = {0U};
  for (size_t i = (size_t)0U; i < LIBCRUX_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE;
       i++) {
    size_t i0 = i;
    uint8_t outi =
        ((uint32_t)Eurydice_slice_index(lhs, i0, uint8_t, uint8_t *) &
         (uint32_t)mask) |
        ((uint32_t)Eurydice_slice_index(rhs, i0, uint8_t, uint8_t *) &
         (uint32_t)~mask);
    out[i0] = outi;
  }
  memcpy(ret, out, (size_t)32U * sizeof(uint8_t));
}

static KRML_NOINLINE void select_shared_secret_in_constant_time(
    Eurydice_slice lhs, Eurydice_slice rhs, uint8_t selector,
    uint8_t ret[32U]) {
  select_ct(lhs, rhs, selector, ret);
}

KRML_NOINLINE void
libcrux_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_slice lhs_c, Eurydice_slice rhs_c, Eurydice_slice lhs_s,
    Eurydice_slice rhs_s, uint8_t ret[32U]) {
  uint8_t selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);
  uint8_t ret0[32U];
  select_shared_secret_in_constant_time(lhs_s, rhs_s, selector, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank) {
  return rank * LIBCRUX_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U;
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t classify_57_90(uint8_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_73_39(int16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
uint8_t libcrux_secrets_int_as_u8_d2(int16_t self) {
  return classify_57_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_57_39(int16_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t

*/
static KRML_MUSTINLINE uint8_t declassify_73_90(uint8_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for u8)}
*/
int16_t libcrux_secrets_int_as_i16_84(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)declassify_73_90(self));
}

/**
 Construct a public integer (identity)
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.secret
with types int16_t

*/
static KRML_MUSTINLINE int16_t secret_39(int16_t x) { return x; }

int16_t libcrux_secrets_int_I16(int16_t v) { return secret_39(v); }

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int32_t

*/
static KRML_MUSTINLINE int32_t classify_57_a8(int32_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
int32_t libcrux_secrets_int_as_i32_d2(int16_t self) {
  return classify_57_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int32_t

*/
static KRML_MUSTINLINE int32_t declassify_73_a8(int32_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for i32)#6}
*/
int16_t libcrux_secrets_int_as_i16_98(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)declassify_73_a8(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t declassify_73_df(uint32_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
int32_t libcrux_secrets_int_as_i32_41(uint32_t self) {
  return classify_57_a8((int32_t)declassify_73_df(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t classify_57_de(uint16_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
uint16_t libcrux_secrets_int_as_u16_d2(int16_t self) {
  return classify_57_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t declassify_73_de(uint16_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
int16_t libcrux_secrets_int_as_i16_e9(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)declassify_73_de(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t classify_57_49(uint64_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for u16)#1}
*/
uint64_t libcrux_secrets_int_as_u64_e9(uint16_t self) {
  return classify_57_49((uint64_t)declassify_73_de(self));
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_57_df(uint32_t self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t declassify_73_49(uint64_t self) { return self; }

/**
This function found in impl {(libcrux_secrets::int::CastOps for u64)#3}
*/
uint32_t libcrux_secrets_int_as_u32_0b(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_57_df(
      (uint32_t)declassify_73_49(self));
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for u32)#2}
*/
int16_t libcrux_secrets_int_as_i16_41(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      (int16_t)declassify_73_df(self));
}

/**
This function found in impl {(libcrux_secrets::int::CastOps for i16)#5}
*/
int16_t libcrux_secrets_int_as_i16_d2(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_57_39(
      libcrux_secrets_int_public_integers_declassify_73_39(self));
}

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair libcrux_ml_kem_types_from_3a_94(
    libcrux_ml_kem_types_MlKemPrivateKey_83 sk,
    libcrux_ml_kem_types_MlKemPublicKey_64 pk) {
  return (KRML_CLITERAL(libcrux_ml_kem_mlkem1024_MlKem1024KeyPair){.sk = sk,
                                                                   .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 3168
*/
libcrux_ml_kem_types_MlKemPrivateKey_83 libcrux_ml_kem_types_from_9a_39(
    uint8_t value[3168U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[3168U];
  memcpy(copy_of_value, value, (size_t)3168U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_83 lit;
  memcpy(lit.value, copy_of_value, (size_t)3168U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_af(
    libcrux_ml_kem_types_MlKemCiphertext_64 *self) {
  return self->value;
}

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair libcrux_ml_kem_types_from_3a_74(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 sk,
    libcrux_ml_kem_types_MlKemPublicKey_30 pk) {
  return (KRML_CLITERAL(libcrux_ml_kem_mlkem768_MlKem768KeyPair){.sk = sk,
                                                                 .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 2400
*/
libcrux_ml_kem_types_MlKemPrivateKey_d9 libcrux_ml_kem_types_from_9a_28(
    uint8_t value[2400U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[2400U];
  memcpy(copy_of_value, value, (size_t)2400U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_d9 lit;
  memcpy(lit.value, copy_of_value, (size_t)2400U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 1088
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return self->value;
}

/**
This function found in impl
{libcrux_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>#21}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_3a
with const generics
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
libcrux_ml_kem_types_MlKemKeyPair_3e libcrux_ml_kem_types_from_3a_fa(
    libcrux_ml_kem_types_MlKemPrivateKey_fa sk,
    libcrux_ml_kem_types_MlKemPublicKey_52 pk) {
  return (
      KRML_CLITERAL(libcrux_ml_kem_types_MlKemKeyPair_3e){.sk = sk, .pk = pk});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPrivateKey<SIZE>)#12}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_9a
with const generics
- SIZE= 1632
*/
libcrux_ml_kem_types_MlKemPrivateKey_fa libcrux_ml_kem_types_from_9a_2a(
    uint8_t value[1632U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1632U];
  memcpy(copy_of_value, value, (size_t)1632U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPrivateKey_fa lit;
  memcpy(lit.value, copy_of_value, (size_t)1632U * sizeof(uint8_t));
  return lit;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemCiphertext<SIZE>#6}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_d4
with const generics
- SIZE= 768
*/
uint8_t *libcrux_ml_kem_types_as_slice_d4_d0(
    libcrux_ml_kem_types_MlKemCiphertext_1a *self) {
  return self->value;
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 1184
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_d0(
    libcrux_ml_kem_types_MlKemPublicKey_30 *self) {
  return self->value;
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 1184
*/
libcrux_ml_kem_types_MlKemPublicKey_30 libcrux_ml_kem_types_from_5f_d0(
    uint8_t value[1184U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1184U];
  memcpy(copy_of_value, value, (size_t)1184U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_30 lit;
  memcpy(lit.value, copy_of_value, (size_t)1184U * sizeof(uint8_t));
  return lit;
}

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_b4(
    Eurydice_slice private_key) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  return (
      KRML_CLITERAL(Eurydice_slice_uint8_t_x4){.fst = ind_cpa_secret_key,
                                               .snd = ind_cpa_public_key,
                                               .thd = ind_cpa_public_key_hash,
                                               .f3 = implicit_rejection_value});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 1088
*/
libcrux_ml_kem_mlkem768_MlKem768Ciphertext libcrux_ml_kem_types_from_00_80(
    uint8_t value[1088U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1088U];
  memcpy(copy_of_value, value, (size_t)1088U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem768_MlKem768Ciphertext lit;
  memcpy(lit.value, copy_of_value, (size_t)1088U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_e0(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator) {
  KRML_MAYBE_FOR3(i, (size_t)0U, (size_t)3U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  return domain_separator;
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 1088
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_80(
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *self) {
  return Eurydice_array_to_slice((size_t)1088U, self->value, uint8_t);
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
void libcrux_ml_kem_utils_into_padded_array_15(Eurydice_slice slice,
                                               uint8_t ret[1120U]) {
  uint8_t out[1120U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)1120U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 800
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_4d(
    libcrux_ml_kem_types_MlKemPublicKey_52 *self) {
  return self->value;
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 800
*/
libcrux_ml_kem_types_MlKemPublicKey_52 libcrux_ml_kem_types_from_5f_4d(
    uint8_t value[800U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[800U];
  memcpy(copy_of_value, value, (size_t)800U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_52 lit;
  memcpy(lit.value, copy_of_value, (size_t)800U * sizeof(uint8_t));
  return lit;
}

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_0c(
    Eurydice_slice private_key) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)768U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)800U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  return (
      KRML_CLITERAL(Eurydice_slice_uint8_t_x4){.fst = ind_cpa_secret_key,
                                               .snd = ind_cpa_public_key,
                                               .thd = ind_cpa_public_key_hash,
                                               .f3 = implicit_rejection_value});
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 768
*/
libcrux_ml_kem_types_MlKemCiphertext_1a libcrux_ml_kem_types_from_00_d0(
    uint8_t value[768U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[768U];
  memcpy(copy_of_value, value, (size_t)768U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_1a lit;
  memcpy(lit.value, copy_of_value, (size_t)768U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 2
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_fd(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator) {
  KRML_MAYBE_FOR2(i, (size_t)0U, (size_t)2U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  return domain_separator;
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 768
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_d0(
    libcrux_ml_kem_types_MlKemCiphertext_1a *self) {
  return Eurydice_array_to_slice((size_t)768U, self->value, uint8_t);
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 800
*/
void libcrux_ml_kem_utils_into_padded_array_4d(Eurydice_slice slice,
                                               uint8_t ret[800U]) {
  uint8_t out[800U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)800U * sizeof(uint8_t));
}

/**
This function found in impl {libcrux_ml_kem::types::MlKemPublicKey<SIZE>#20}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_slice_fd
with const generics
- SIZE= 1568
*/
uint8_t *libcrux_ml_kem_types_as_slice_fd_af(
    libcrux_ml_kem_types_MlKemPublicKey_64 *self) {
  return self->value;
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemPublicKey<SIZE>)#19}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_5f
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemPublicKey_64 libcrux_ml_kem_types_from_5f_af(
    uint8_t value[1568U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1568U];
  memcpy(copy_of_value, value, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemPublicKey_64 lit;
  memcpy(lit.value, copy_of_value, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_slice_uint8_t_x4 libcrux_ml_kem_types_unpack_private_key_1f(
    Eurydice_slice private_key) {
  Eurydice_slice_uint8_t_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1536U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_secret_key = uu____0.fst;
  Eurydice_slice secret_key0 = uu____0.snd;
  Eurydice_slice_uint8_t_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1568U, uint8_t, Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key = uu____1.fst;
  Eurydice_slice secret_key = uu____1.snd;
  Eurydice_slice_uint8_t_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_slice_uint8_t_x2);
  Eurydice_slice ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_slice implicit_rejection_value = uu____2.snd;
  return (
      KRML_CLITERAL(Eurydice_slice_uint8_t_x4){.fst = ind_cpa_secret_key,
                                               .snd = ind_cpa_public_key,
                                               .thd = ind_cpa_public_key_hash,
                                               .f3 = implicit_rejection_value});
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[32size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_b3(core_result_Result_fb self, uint8_t ret[32U]) {
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

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
void libcrux_ml_kem_utils_into_padded_array_b6(Eurydice_slice slice,
                                               uint8_t ret[34U]) {
  uint8_t out[34U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)34U * sizeof(uint8_t));
}

/**
This function found in impl {(core::convert::From<@Array<u8, SIZE>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#5}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.from_00
with const generics
- SIZE= 1568
*/
libcrux_ml_kem_types_MlKemCiphertext_64 libcrux_ml_kem_types_from_00_af(
    uint8_t value[1568U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_value[1568U];
  memcpy(copy_of_value, value, (size_t)1568U * sizeof(uint8_t));
  libcrux_ml_kem_types_MlKemCiphertext_64 lit;
  memcpy(lit.value, copy_of_value, (size_t)1568U * sizeof(uint8_t));
  return lit;
}

/**
A monomorphic instance of libcrux_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_ml_kem_utils_prf_input_inc_ac(uint8_t (*prf_inputs)[33U],
                                              uint8_t domain_separator) {
  KRML_MAYBE_FOR4(i, (size_t)0U, (size_t)4U, (size_t)1U, size_t i0 = i;
                  prf_inputs[i0][32U] = domain_separator;
                  domain_separator = (uint32_t)domain_separator + 1U;);
  return domain_separator;
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
void libcrux_ml_kem_utils_into_padded_array_c8(Eurydice_slice slice,
                                               uint8_t ret[33U]) {
  uint8_t out[33U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)33U * sizeof(uint8_t));
}

/**
This function found in impl {(core::convert::AsRef<@Slice<u8>> for
libcrux_ml_kem::types::MlKemCiphertext<SIZE>)#4}
*/
/**
A monomorphic instance of libcrux_ml_kem.types.as_ref_43
with const generics
- SIZE= 1568
*/
Eurydice_slice libcrux_ml_kem_types_as_ref_43_af(
    libcrux_ml_kem_types_MlKemCiphertext_64 *self) {
  return Eurydice_array_to_slice((size_t)1568U, self->value, uint8_t);
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
void libcrux_ml_kem_utils_into_padded_array_7f(Eurydice_slice slice,
                                               uint8_t ret[1600U]) {
  uint8_t out[1600U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)1600U * sizeof(uint8_t));
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
void libcrux_ml_kem_utils_into_padded_array_24(Eurydice_slice slice,
                                               uint8_t ret[64U]) {
  uint8_t out[64U] = {0U};
  uint8_t *uu____0 = out;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice2(uu____0, (size_t)0U,
                                  Eurydice_slice_len(slice, uint8_t), uint8_t),
      slice, uint8_t);
  memcpy(ret, out, (size_t)64U * sizeof(uint8_t));
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[24size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_70(core_result_Result_b2 self, uint8_t ret[24U]) {
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

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[20size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_20(core_result_Result_e1 self, uint8_t ret[20U]) {
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

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[10size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_ce(core_result_Result_9d self, uint8_t ret[10U]) {
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

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[24size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_d2(uint8_t self[24U],
                                                          uint8_t ret[24U]) {
  memcpy(ret, self, (size_t)24U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[20size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_57(uint8_t self[20U],
                                                          uint8_t ret[20U]) {
  memcpy(ret, self, (size_t)20U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[10size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_cc(uint8_t self[10U],
                                                          uint8_t ret[10U]) {
  memcpy(ret, self, (size_t)10U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[8size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_76(uint8_t self[8U],
                                                          uint8_t ret[8U]) {
  memcpy(ret, self, (size_t)8U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[2size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_d4(uint8_t self[2U],
                                                          uint8_t ret[2U]) {
  memcpy(ret, self, (size_t)2U * sizeof(uint8_t));
}

/**
 Classify a mutable slice (identity)
 We define a separate function for this because hax has limited support for
 &mut-returning functions
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_mut_slice
with types Eurydice_slice uint8_t

*/
Eurydice_slice libcrux_secrets_int_public_integers_classify_mut_slice_ba(
    Eurydice_slice x) {
  return x;
}

/**
This function found in impl {(libcrux_secrets::traits::Classify<T> for T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_57
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_classify_57_46(int16_t self[16U],
                                                        int16_t ret[16U]) {
  memcpy(ret, self, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types int16_t[16size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_46(int16_t self[16U],
                                                          int16_t ret[16U]) {
  memcpy(ret, self, (size_t)16U * sizeof(int16_t));
}

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice uint8_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_b8_ba(
    Eurydice_slice *self) {
  return self;
}

/**
This function found in impl {(libcrux_secrets::traits::Declassify<T> for T)#1}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_73
with types uint8_t[22size_t]

*/
void libcrux_secrets_int_public_integers_declassify_73_fa(uint8_t self[22U],
                                                          uint8_t ret[22U]) {
  memcpy(ret, self, (size_t)22U * sizeof(uint8_t));
}

/**
This function found in impl {(libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T))#2}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_b8
with types Eurydice_slice int16_t

*/
Eurydice_slice *libcrux_secrets_int_public_integers_classify_ref_b8_03(
    Eurydice_slice *self) {
  return self;
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types int16_t[16size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_00(core_result_Result_0a self, int16_t ret[16U]) {
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

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types uint8_t[8size_t], core_array_TryFromSliceError

*/
void core_result_unwrap_26_68(core_result_Result_15 self, uint8_t ret[8U]) {
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
