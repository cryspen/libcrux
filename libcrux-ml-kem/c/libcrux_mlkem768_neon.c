/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: c66a520f7072006af0071eb517002a73d5f3a7d1
 * Eurydice: 9dae7cbf24d38b7b0eb8e7efd12d662a4ebe1f1a
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: fba8ff3916a9aa0a3869f2fffea66d8aea07144a
 */

#include "internal/libcrux_mlkem768_neon.h"

#include "internal/libcrux_mlkem_neon.h"
#include "libcrux_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.neon.decapsulate
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
static Eurydice_arr_60 decapsulate_35(Eurydice_arr_ea *private_key,
                                      Eurydice_arr_2c *ciphertext) {
  return libcrux_ml_kem_ind_cca_decapsulate_760(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem768_neon_decapsulate(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  return decapsulate_35(private_key, ciphertext);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.neon.encapsulate
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
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
*/
static tuple_56 encapsulate_cd(Eurydice_arr_74 *public_key,
                               Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_990(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_56 libcrux_ml_kem_mlkem768_neon_encapsulate(Eurydice_arr_74 *public_key,
                                                  Eurydice_arr_60 randomness) {
  return encapsulate_cd(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.generate_keypair with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem768_MlKem768KeyPair generate_keypair_ce(
    libcrux_sha3_Sha3_512Digest *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_580(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_neon_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  return generate_keypair_ce(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.validate_private_key with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool validate_private_key_31(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_a5(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_private_key(
    Eurydice_arr_ea *private_key, Eurydice_arr_2c *ciphertext) {
  return validate_private_key_31(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.validate_private_key_only with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool validate_private_key_only_41(
    Eurydice_arr_ea *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_20(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_private_key_only(
    Eurydice_arr_ea *private_key) {
  return validate_private_key_only_41(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.validate_public_key with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool validate_public_key_41(
    Eurydice_arr_74 *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_21(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_neon_validate_public_key(
    Eurydice_arr_74 *public_key) {
  return validate_public_key_41(public_key);
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.unpacked.decapsulate with const
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
static KRML_MUSTINLINE Eurydice_arr_60 decapsulate_350(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_2c *ciphertext) {
  return libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa0(key_pair, ciphertext);
}

/**
 Decapsulate ML-KEM 768 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem768KeyPairUnpacked`] and an [`MlKem768Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem768_neon_unpacked_decapsulate(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *private_key,
    Eurydice_arr_2c *ciphertext) {
  return decapsulate_350(private_key, ciphertext);
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.unpacked.encapsulate with const
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
static KRML_MUSTINLINE tuple_56 encapsulate_cd0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_550(public_key,
                                                         randomness);
}

/**
 Encapsulate ML-KEM 768 (unpacked)

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem768PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_56 libcrux_ml_kem_mlkem768_neon_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_60 randomness) {
  return encapsulate_cd0(public_key, &randomness);
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.unpacked.generate_keypair with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static KRML_MUSTINLINE void generate_keypair_ce0(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *out) {
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_580(randomness, out);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  generate_keypair_ce0(randomness, key_pair);
}

/**
 Generate ML-KEM 768 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_neon_unpacked_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_7b_a5();
  libcrux_ml_kem_mlkem768_neon_unpacked_generate_key_pair_mut(randomness,
                                                              &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_mlkem768_neon_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_7b_a5();
}

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
libcrux_ml_kem_mlkem768_neon_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_30_a5();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.unpacked.keypair_from_private_key
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
static KRML_MUSTINLINE void keypair_from_private_key_fd(
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_36(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_key_pair_from_private_mut(
    Eurydice_arr_ea *private_key,
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  keypair_from_private_key_fd(private_key, key_pair);
}

/**
 Get the serialized private key.
*/
Eurydice_arr_ea
libcrux_ml_kem_mlkem768_neon_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_b0(key_pair);
}

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_ea *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_b0(key_pair,
                                                                   serialized);
}

/**
 Get the serialized public key.
*/
Eurydice_arr_74
libcrux_ml_kem_mlkem768_neon_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_21(key_pair);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
    Eurydice_arr_74 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_21(key_pair,
                                                                  serialized);
}

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_public_key(
    libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *pk) {
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec uu____0 =
      libcrux_ml_kem_ind_cca_unpacked_clone_d7_a5(
          libcrux_ml_kem_ind_cca_unpacked_public_key_11_a5(key_pair));
  pk[0U] = uu____0;
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *public_key,
    Eurydice_arr_74 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_21(public_key, serialized);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.neon.unpacked.unpack_public_key with const
generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void unpack_public_key_31(
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e0(public_key,
                                                        unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem768_neon_unpacked_unpacked_public_key(
    Eurydice_arr_74 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
        *unpacked_public_key) {
  unpack_public_key_31(public_key, unpacked_public_key);
}
