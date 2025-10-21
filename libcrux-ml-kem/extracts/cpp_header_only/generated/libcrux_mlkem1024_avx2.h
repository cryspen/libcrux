/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 92c93e1cb1aa299c44eb039374098c8dd598c640
 * Eurydice: 1a15deb0a4af5c10c90c974891a6300b57adef8b
 * Karamel: d55e3f86aa758514f610dfe74f4f1807cdc7244f
 * F*: unset
 * Libcrux: 868c4c3b985fcc32521211b51b06eccb46d9a6ad
 */

#ifndef libcrux_mlkem1024_avx2_H
#define libcrux_mlkem1024_avx2_H

#include "eurydice_glue.h"
#include "intrinsics/libcrux_intrinsics_avx2.h"
#include "libcrux_mlkem768_avx2.h"
#include "libcrux_mlkem_core.h"

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Eurydice_arr_600 libcrux_ml_kem_mlkem1024_avx2_decapsulate(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_decapsulate_e0(private_key,
                                                                   ciphertext);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_2b libcrux_ml_kem_mlkem1024_avx2_encapsulate(
    Eurydice_arr_00 *public_key, Eurydice_arr_600 randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_encapsulate_8f(public_key,
                                                                   &randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_avx2_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_generate_keypair_b4(
      &randomness);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem1024_avx2_validate_private_key(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_6b(
      private_key, ciphertext);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem1024_avx2_validate_private_key_only(
    Eurydice_arr_17 *private_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_private_key_only_44(
      private_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline bool libcrux_ml_kem_mlkem1024_avx2_validate_public_key(
    Eurydice_arr_00 *public_key) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_validate_public_key_44(
      public_key);
}

/**
 Decapsulate ML-KEM 1024 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem1024KeyPairUnpacked`] and an [`MlKem1024Ciphertext`].
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Eurydice_arr_600
libcrux_ml_kem_mlkem1024_avx2_unpacked_decapsulate(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
        *private_key,
    Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_decapsulate_e0(
      private_key, ciphertext);
}

/**
 Encapsulate ML-KEM 1024 (unpacked)

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem1024PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
 TODO: The F* prefix opens required modules, it should go away when the
 following issue is resolved: <https://github.com/hacspec/hax/issues/770>
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline tuple_2b libcrux_ml_kem_mlkem1024_avx2_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_600 randomness) {
  return libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_encapsulate_8f(
      public_key, &randomness);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem1024_avx2_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_generate_keypair_b4(
      randomness, key_pair);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_mlkem1024_avx2_unpacked_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_7b_42();
  libcrux_ml_kem_mlkem1024_avx2_unpacked_generate_key_pair_mut(randomness,
                                                               &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_mlkem1024_avx2_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_7b_42();
}

/**
 Create a new, empty unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
libcrux_ml_kem_mlkem1024_avx2_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_30_42();
}

/**
 Get an unpacked key from a private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_from_private_mut(
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_keypair_from_private_key_b4(
      private_key, key_pair);
}

/**
 Get the serialized private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Eurydice_arr_17
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_c9(key_pair);
}

/**
 Get the serialized private key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_17 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_c9(key_pair,
                                                                   serialized);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline Eurydice_arr_00
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_78(key_pair);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_78(key_pair,
                                                                  serialized);
}

/**
 Get the serialized public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem1024_avx2_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_78(public_key, serialized);
}

/**
 Get the unpacked public key.
*/
KRML_ATTRIBUTE_TARGET("avx2")
static inline void libcrux_ml_kem_mlkem1024_avx2_unpacked_unpacked_public_key(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_instantiations_avx2_unpacked_unpack_public_key_6b(
      public_key, unpacked_public_key);
}

typedef libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024PublicKeyUnpacked;

#define libcrux_mlkem1024_avx2_H_DEFINED
#endif /* libcrux_mlkem1024_avx2_H */
