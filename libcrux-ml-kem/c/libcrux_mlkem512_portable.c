/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 8de6020c10a3520a56fbf849176f8218e62435cf
 * Eurydice: f8fc97aeb6ecbaaacfe4baffcdc4d671989b5586
 * Karamel: 98e5d604741a886e20a526f6673077a15e23cead
 * F*: 58c915a86a2c07c8eca8d9deafd76cb7a91f0eb7
 * Libcrux: 0c66762ad2fdfb3f110ee362fa210bea0fecd265
 */

#include "libcrux_mlkem512_portable.h"

#include "internal/libcrux_mlkem_portable.h"

/**
 Portable decapsulate
*/
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
static void decapsulate_04(libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
                           libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext,
                           uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_b00(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_5e *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_04(private_key, ciphertext, ret);
}

/**
 Portable decapsulate
*/
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
static void decapsulate_unpacked_d1(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_unpacked_de0(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 512 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem512KeyPairUnpacked`] and an [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_portable_decapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_e8 *ciphertext, uint8_t ret[32U]) {
  decapsulate_unpacked_d1(private_key, ciphertext, ret);
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
- VECTOR_U_BLOCK_LEN= 320
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
*/
static tuple_ec encapsulate_0e(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_780(uu____0, copy_of_randomness);
}

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_be *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_types_MlKemPublicKey_be *uu____0 = public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_0e(uu____0, copy_of_randomness);
}

/**
 Portable encapsualte
*/
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
static tuple_ec encapsulate_unpacked_2c(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_encapsulate_unpacked_080(uu____0,
                                                         copy_of_randomness);
}

/**
 Encapsulate ML-KEM 512 (unpacked)

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem512PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_ec libcrux_ml_kem_mlkem512_portable_encapsulate_unpacked(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *public_key,
    uint8_t randomness[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ae *uu____0 =
      public_key;
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[32U];
  memcpy(copy_of_randomness, randomness, (size_t)32U * sizeof(uint8_t));
  return encapsulate_unpacked_2c(uu____0, copy_of_randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- BYTES_PER_RING_ELEMENT= 768
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_types_MlKemKeyPair_cb generate_keypair_33(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_d70(copy_of_randomness);
}

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_cb
libcrux_ml_kem_mlkem512_portable_generate_key_pair(uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_33(copy_of_randomness);
}

/**
 Unpacked API
*/
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
generate_keypair_unpacked_fe(uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return libcrux_ml_kem_ind_cca_generate_keypair_unpacked_370(
      copy_of_randomness);
}

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked_ae
libcrux_ml_kem_mlkem512_portable_generate_key_pair_unpacked(
    uint8_t randomness[64U]) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  return generate_keypair_unpacked_fe(copy_of_randomness);
}

/**
 Portable public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 2
- RANKED_BYTES_PER_RING_ELEMENT= 768
- PUBLIC_KEY_SIZE= 800
*/
static bool validate_public_key_240(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_3f0(public_key);
}

/**
 Validate a public key.

 Returns `Some(public_key)` if valid, and `None` otherwise.
*/
core_option_Option_04 libcrux_ml_kem_mlkem512_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_be public_key) {
  core_option_Option_04 uu____0;
  if (validate_public_key_240(public_key.value)) {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_Some,
                                               .f0 = public_key});
  } else {
    uu____0 = (CLITERAL(core_option_Option_04){.tag = core_option_None});
  }
  return uu____0;
}
