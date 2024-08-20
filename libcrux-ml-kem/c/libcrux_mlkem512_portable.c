/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 3f6d1c304e0e5bef1e9e2ea65aec703661b05f39
 * Eurydice: 392674166bac86e60f5fffa861181a398fdc3896
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: 3ed3c98d39ce028c31c5908a38bc68ad5098f563
 * Libcrux: d6111233152fe392e83036ad6c29da60f591aef9
 */

#include "libcrux_mlkem512_portable.h"

#include "internal/libcrux_mlkem_portable.h"

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics
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
static void decapsulate_4a(libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
                           libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext,
                           uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_e30(private_key, ciphertext, ret);
}

void libcrux_ml_kem_mlkem512_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_4a(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate_unpacked with const
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
static void decapsulate_unpacked_d4(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_unpacked_5e0(key_pair, ciphertext,
                                                           ret);
}

void libcrux_ml_kem_mlkem512_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_unpacked_d4(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics
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
static tuple_ec encapsulate_7d(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_440(uu____0, uu____1);
}

tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_7d(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate_unpacked with const
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
static tuple_ec encapsulate_unpacked_84(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_unpacked_840(uu____0,
                                                                  uu____1);
}

tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_84(uu____0, uu____1);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- RANKED_BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_types_MlKemKeyPair_cb generate_keypair_df(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_c21(uu____0);
}

libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_portable_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_df(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair_unpacked with
const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae
generate_keypair_unpacked_bc(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_unpacked_generate_keypair_unpacked_480(uu____0);
}

libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae
libcrux_ml_kem_mlkem512_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_bc(uu____0);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static bool validate_public_key_e10(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_350(public_key);
}

core_option_Option_04 libcrux_ml_kem_mlkem512_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key) {
  core_option_Option_04 uu____0;
  if (validate_public_key_e10(public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_None});
  }
  return uu____0;
}
