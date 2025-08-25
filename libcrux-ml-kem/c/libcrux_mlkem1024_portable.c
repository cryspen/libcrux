/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: ac1a7e957d0dbcab6ae1a948e08b7a16b557851d
 * Karamel: 354791911c6b40d15a41cda7a0e3560da1cf31a1
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: d21c4cc2a58bda0db52962f7b838e8bde470f16b
 */

#include "internal/libcrux_mlkem1024_portable.h"

#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics
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
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_621(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
void libcrux_ml_kem_mlkem1024_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_e0(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
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
*/
static tuple_fa encapsulate_8f(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_ca1(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_fa libcrux_ml_kem_mlkem1024_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
    uint8_t randomness[32U]) {
  return encapsulate_8f(public_key, randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_b4(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_151(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(uint8_t randomness[64U]) {
  return generate_keypair_b4(randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key with const
generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_private_key_6b(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_b5(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext) {
  return validate_private_key_6b(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key_only with
const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
static KRML_MUSTINLINE bool validate_private_key_only_44(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_60(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key) {
  return validate_private_key_only_44(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_public_key_44(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_ff(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key) {
  return validate_public_key_44(public_key->value);
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.decapsulate with const
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
static KRML_MUSTINLINE void decapsulate_e00(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_unpacked_decapsulate_511(key_pair, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem1024KeyPairUnpacked`] and an [`MlKem1024Ciphertext`].
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_decapsulate(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext,
    uint8_t ret[32U]) {
  decapsulate_e00(private_key, ciphertext, ret);
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.encapsulate with const
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
static KRML_MUSTINLINE tuple_fa encapsulate_8f0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *public_key,
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c1(public_key,
                                                         randomness);
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
tuple_fa libcrux_ml_kem_mlkem1024_portable_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *public_key,
    uint8_t randomness[32U]) {
  return encapsulate_8f0(public_key, randomness);
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.generate_keypair with
const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_b40(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked *out) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_151(copy_of_randomness, out);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_generate_key_pair_mut(
    uint8_t randomness[64U],
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  /* Passing arrays by value in Rust generates a copy in C */
  uint8_t copy_of_randomness[64U];
  memcpy(copy_of_randomness, randomness, (size_t)64U * sizeof(uint8_t));
  generate_keypair_b40(copy_of_randomness, key_pair);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_mlkem1024_portable_unpacked_generate_key_pair(
    uint8_t randomness[64U]) {
  libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_7b_d0();
  uint8_t uu____0[64U];
  memcpy(uu____0, randomness, (size_t)64U * sizeof(uint8_t));
  libcrux_ml_kem_mlkem1024_portable_unpacked_generate_key_pair_mut(uu____0,
                                                                   &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_mlkem1024_portable_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_7b_d0();
}

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
libcrux_ml_kem_mlkem1024_portable_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_30_d0();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.keypair_from_private_key
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void keypair_from_private_key_b4(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_7d(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_key_pair_from_private_mut(
    libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  keypair_from_private_key_b4(private_key, key_pair);
}

/**
 Get the serialized private key.
*/
libcrux_ml_kem_types_MlKemPrivateKey_83
libcrux_ml_kem_mlkem1024_portable_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_2f(key_pair);
}

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair,
    libcrux_ml_kem_types_MlKemPrivateKey_83 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_2f(key_pair,
                                                                   serialized);
}

/**
 Get the serialized public key.
*/
libcrux_ml_kem_types_MlKemPublicKey_64
libcrux_ml_kem_mlkem1024_portable_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_ff(key_pair);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem1024_portable_unpacked_MlKem1024KeyPairUnpacked
        *key_pair,
    libcrux_ml_kem_types_MlKemPublicKey_64 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_ff(key_pair,
                                                                  serialized);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af *public_key,
    libcrux_ml_kem_types_MlKemPublicKey_64 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_ff(public_key, serialized);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.unpack_public_key with
const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void unpack_public_key_6b(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_30(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem1024_portable_unpacked_unpacked_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_af
        *unpacked_public_key) {
  unpack_public_key_6b(public_key, unpacked_public_key);
}
