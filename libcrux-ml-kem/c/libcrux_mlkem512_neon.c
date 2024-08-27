/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: 04413e808445c4f78fe89cd15b85ff549ed3be62
 * Libcrux: 1ecfc745f64e318b06fd59a787d07818640c56cc
 */

#include "libcrux_mlkem512_neon.h"

#include "internal/libcrux_mlkem_neon.h"

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.neon.decapsulate
with const generics
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
static void decapsulate_b6(libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
                           libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext,
                           uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_9c1(private_key, ciphertext, ret);
}

void libcrux_ml_kem_mlkem512_neon_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_b6(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.decapsulate_unpacked with const
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
static void decapsulate_unpacked_ee(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66 *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_dc1(key_pair, ciphertext,
                                                           ret);
}

void libcrux_ml_kem_mlkem512_neon_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66 *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_unpacked_ee(private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.neon.encapsulate
with const generics
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
static tuple_ec encapsulate_e7(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_ff1(uu____0, uu____1);
}

tuple_ec libcrux_ml_kem_mlkem512_neon_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_e7(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.encapsulate_unpacked with const
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
static tuple_ec encapsulate_unpacked_ec(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_cf1(uu____0,
                                                                  uu____1);
}

tuple_ec libcrux_ml_kem_mlkem512_neon_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_66 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_ec(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.generate_keypair with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_types_MlKemKeyPair_cb generate_keypair_25(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_ec1(uu____0);
}

libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_neon_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_25(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.generate_keypair_unpacked with const
generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66
generate_keypair_unpacked_29(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_a51(uu____0);
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_66
libcrux_ml_kem_mlkem512_neon_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_29(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.validate_public_key with const
generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static bool validate_public_key_2c1(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_991(public_key);
}

core_option_Option_04 libcrux_ml_kem_mlkem512_neon_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key) {
  core_option_Option_04 uu____0;
  if (validate_public_key_2c1(public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_None});
  }
  return uu____0;
}
