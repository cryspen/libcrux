/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 0eb8a17354fd62586cb9f7515af23f4488c2267e
 * Karamel: 1ed8ba551e8c65fdbad1bb7833bd7837be0d89b9
 * F*: a32b316e521fa4f239b610ec8f1d15e78d62cbe8-dirty
 * Libcrux: 59864a878d97174338edf8868672aac0555a8814
 */

#include "libcrux_mlkem512_avx2.h"

#include "internal/libcrux_mlkem_avx2.h"

static void
decapsulate___2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_ind_cca_decapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
      private_key, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_mlkem512_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  decapsulate___2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
      private_key, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static void
decapsulate_unpacked___2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  libcrux_ml_kem_ind_cca_decapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
      key_pair, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

void libcrux_ml_kem_mlkem512_avx2_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  uint8_t ret0[32U];
  decapsulate_unpacked___2size_t_1632size_t_768size_t_800size_t_768size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t_800size_t(
      private_key, ciphertext, ret0);
  memcpy(ret, ret0, (size_t)32U * sizeof(uint8_t));
}

static K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
encapsulate___2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____800size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_libcrux_ml_kem_ind_cca_MlKem_2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem512_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____800size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate___2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____0, uu____1);
}

static K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
encapsulate_unpacked___2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem512_avx2_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked___2size_t_768size_t_800size_t_768size_t_640size_t_128size_t_10size_t_4size_t_320size_t_3size_t_192size_t_2size_t_128size_t(
      uu____0, uu____1);
}

static libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
generate_keypair___2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
      uu____0);
}

libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_mlkem512_avx2_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair___2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
      uu____0);
}

static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
generate_keypair_unpacked___2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector_libcrux_ml_kem_hash_functions_avx2_Simd256Hash_2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
      uu____0);
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_avx2_SIMD256Vector__2size_t
libcrux_ml_kem_mlkem512_avx2_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked___2size_t_768size_t_1632size_t_800size_t_768size_t_3size_t_192size_t(
      uu____0);
}

static bool validate_public_key___2size_t_768size_t_800size_t(
    uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key__libcrux_ml_kem_vector_avx2_SIMD256Vector_2size_t_768size_t_800size_t(
      public_key);
}

core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__
libcrux_ml_kem_mlkem512_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t public_key) {
  core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__ uu____0;
  if (validate_public_key___2size_t_768size_t_800size_t(public_key.value)) {
    uu____0 = (CLITERAL(
        core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__){
        .tag = core_option_Some, .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(
        core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__){
        .tag = core_option_None});
  }
  return uu____0;
}
