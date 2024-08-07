/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 53530427db2941ce784201e64086766504bc5642
 * Eurydice: f4283998bcc3c86677cf0e03a6fa71913a524658
 * Karamel: fc56fce6a58754766809845f88fc62063b2c6b92
 * F*: e5cef6f266ece8a8b55ef4cd9b61cdf103520d38
 * Libcrux: 878f09c21a4312320518388a0d902986b08e030a
 */

#include "libcrux_mlkem1024_avx2.h"

#include "internal/libcrux_mlkem_avx2.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate
with const generics
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
static void decapsulate_e0(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_0b0(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
void libcrux_ml_kem_mlkem1024_avx2_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_95 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_e0(private_key, ciphertext, ret);
}

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate_unpacked with const
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
static void decapsulate_unpacked_5f(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_unpacked_690(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem1024KeyPairUnpacked`] and an [`MlKem1024Ciphertext`].
*/
void libcrux_ml_kem_mlkem1024_avx2_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_unpacked_5f(private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate
with const generics
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
static tuple_21 encapsulate_4f(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_1f *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_910(uu____0, uu____1);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_21 libcrux_ml_kem_mlkem1024_avx2_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_1f *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_1f *uu____0 = public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_4f(uu____0, uu____1);
}

/**
 Portable encapsualte
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate_unpacked with const
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
static tuple_21 encapsulate_unpacked_70(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked_5f0(uu____0, uu____1);
}

/**
 Encapsulate ML-KEM 1024 (unpacked)

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem1024PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
 TODO: The F* prefix opens required modules, it should go away when the
 following issue is resolved: https://github.com/hacspec/hax/issues/770
*/
tuple_21 libcrux_ml_kem_mlkem1024_avx2_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_01 *uu____0 =
      public_key;
  uint8_t uu____1[32U];
  memcpy(uu____1, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_70(uu____0, uu____1);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_e9(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_310(uu____0);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_avx2_generate_key_pair(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_e9(uu____0);
}

/**
 Unpacked API
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair_unpacked with const
generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- BYTES_PER_RING_ELEMENT= 1536
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01
generate_keypair_unpacked_a4(uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked_d30(uu____0);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_01
libcrux_ml_kem_mlkem1024_avx2_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_a4(uu____0);
}

/**
 Portable public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 4
- RANKED_BYTES_PER_RING_ELEMENT= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static bool validate_public_key_cc0(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_9e0(public_key);
}

/**
 Validate a public key.

 Returns `Some(public_key)` if valid, and `None` otherwise.
*/
core_option_Option_99 libcrux_ml_kem_mlkem1024_avx2_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_1f public_key) {
  core_option_Option_99 uu____0;
  if (validate_public_key_cc0(public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_99){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_99){.tag = core_option_None});
  }
  return uu____0;
}
