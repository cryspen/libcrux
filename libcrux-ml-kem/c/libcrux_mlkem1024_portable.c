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

#include "libcrux_mlkem1024_portable.h"

#include "internal/libcrux_mlkem_portable.h"

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics:
- K = 4
- SECRET_KEY_SIZE = 3168
- CPA_SECRET_KEY_SIZE = 1536
- PUBLIC_KEY_SIZE = 1568
- CIPHERTEXT_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- C1_BLOCK_SIZE = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1600
*/
static void decapsulate_f0(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_12(private_key, ciphertext, ret);
}

void libcrux_ml_kem_mlkem1024_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_f0(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate_unpacked with const
generics:
- K = 4
- SECRET_KEY_SIZE = 3168
- CPA_SECRET_KEY_SIZE = 1536
- PUBLIC_KEY_SIZE = 1568
- CIPHERTEXT_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- C1_BLOCK_SIZE = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1600
*/
static void decapsulate_unpacked_f0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_unpacked_23(key_pair, ciphertext, ret);
}

void libcrux_ml_kem_mlkem1024_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_unpacked_f0(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics:
- K = 4
- CIPHERTEXT_SIZE = 1568
- PUBLIC_KEY_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- VECTOR_U_BLOCK_LEN = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
static K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
encapsulate_03(libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
               uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____1568size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_12(uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey____1568size_t *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_03(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate_unpacked with const
generics:
- K = 4
- CIPHERTEXT_SIZE = 1568
- PUBLIC_KEY_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- VECTOR_U_BLOCK_LEN = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
static K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
encapsulate_unpacked_03(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked_23(uu____0, uu____1);
}

K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_mlkem1024_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
      *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_03(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_d7(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_23(uu____0);
}

libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_d7(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair_unpacked with
const generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
generate_keypair_unpacked_d7(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked_23(uu____0);
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
libcrux_ml_kem_mlkem1024_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_d7(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics:
- K = 4
- RANKED_BYTES_PER_RING_ELEMENT = 1536
- PUBLIC_KEY_SIZE = 1568
*/
static bool validate_public_key_65(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_38(public_key);
}

core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__
libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t public_key) {
  core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__
      uu____0;
  if (validate_public_key_65(public_key.value)) {
    uu____0 = (CLITERAL(
        core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__){
        .tag = core_option_Some, .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(
        core_option_Option__libcrux_ml_kem_types_MlKemPublicKey___1568size_t__){
        .tag = core_option_None});
  }
  return uu____0;
}
