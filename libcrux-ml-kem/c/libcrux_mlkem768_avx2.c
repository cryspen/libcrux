/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: d6e4d1bb9c27c4eebbebcb29ba8bea1d58741421
 * Karamel: 2bd16e63cfbfa2b81d3c45d597b811ca2a12d430
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: a7de672380a622d67efb35e3707a528e375cbf76
 */

#include "libcrux_mlkem768_avx2.h"

#include "internal/libcrux_mlkem_avx2.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate
with const generics
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
static void decapsulate_03(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_0b1(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
void libcrux_ml_kem_mlkem768_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_55 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  decapsulate_03(private_key, ciphertext, ret);
}

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate_unpacked with const
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
static void decapsulate_unpacked_cc(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_unpacked_691(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
void libcrux_ml_kem_mlkem768_avx2_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  decapsulate_unpacked_cc(private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate
with const generics
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
static tuple_3c encapsulate_e6(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_911(uu____0, uu____1);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_3c libcrux_ml_kem_mlkem768_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_15 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_15 *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_e6(uu____0, uu____1);
}

/**
 Portable encapsualte
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate_unpacked with const
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
static tuple_3c encapsulate_unpacked_ed(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked_5f1(uu____0, uu____1);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_3c libcrux_ml_kem_mlkem768_avx2_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_a0 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_ed(uu____0, uu____1);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem768_MlKem768KeyPair generate_keypair_1d(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_311(uu____0);
}

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_avx2_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_1d(uu____0);
}

/**
 Unpacked API
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair_unpacked with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- BYTES_PER_RING_ELEMENT= 1152
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
generate_keypair_unpacked_07(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked_d31(uu____0);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_a0
libcrux_ml_kem_mlkem768_avx2_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_07(uu____0);
}

/**
 Portable public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 3
- RANKED_BYTES_PER_RING_ELEMENT= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static bool validate_public_key_cc1(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_9e1(public_key);
}

/**
 Validate a public key.

 Returns `Some(public_key)` if valid, and `None` otherwise.
*/
core_option_Option_92 libcrux_ml_kem_mlkem768_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_15 public_key) {
  core_option_Option_92 uu____0;
  if (validate_public_key_cc1(public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_92){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_92){.tag = core_option_None});
  }
  return uu____0;
}
