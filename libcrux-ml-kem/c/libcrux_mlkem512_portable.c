/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 013beb9e4046a151131c6a56dfe25e606b49c4a1
 * Karamel: 4626e5fcb3787a47c806d160539342ade4b0809c
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: 8a3c1c4c84f258580d53bfef5ad2b1b7d5ef5fca
 */

#include "libcrux_mlkem512_portable.h"

#include "internal/libcrux_mlkem_portable.h"

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics:
- K = 2
- SECRET_KEY_SIZE = 1632
- CPA_SECRET_KEY_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- CIPHERTEXT_SIZE = 768
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 800
*/
static void decapsulate_c4(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_8f(private_key, ciphertext, ret);
}

void libcrux_ml_kem_mlkem512_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_c4(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate_unpacked with const
generics:
- K = 2
- SECRET_KEY_SIZE = 1632
- CPA_SECRET_KEY_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- CIPHERTEXT_SIZE = 768
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 800
*/
static void decapsulate_unpacked_c4(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_unpacked_60(key_pair, ciphertext, ret);
}

void libcrux_ml_kem_mlkem512_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_unpacked_c4(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics:
- K = 2
- CIPHERTEXT_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
static K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
encapsulate_ca(libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
               uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____800size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_8f(uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem512_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____800size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_ca(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate_unpacked with const
generics:
- K = 2
- CIPHERTEXT_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
static K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
encapsulate_unpacked_ca(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked_60(uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem512_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_ca(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
*/
static libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
generate_keypair_0d(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_60(uu____0);
}

libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_mlkem512_portable_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_0d(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair_unpacked with
const generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
generate_keypair_unpacked_0d(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked_60(uu____0);
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
libcrux_ml_kem_mlkem512_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_0d(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics:
- K = 2
- RANKED_BYTES_PER_RING_ELEMENT = 768
- PUBLIC_KEY_SIZE = 800
*/
static bool validate_public_key_35(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_6b(public_key);
}

core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__
libcrux_ml_kem_mlkem512_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t public_key) {
  core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___800size_t__ uu____0;
  if (validate_public_key_35(public_key.value)) {
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
