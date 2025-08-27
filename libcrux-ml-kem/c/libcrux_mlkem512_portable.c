/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 0ea51402a88c38d63f6f815fbe5a6dddb14cf16b
 * Eurydice: 3c77f1ac8116257d0c416fdac562edfa178b860b
 * Karamel: b2cba1e3f23fd7a54cf0b515f95089cfba8d39c3
 * F*: f3a2732c1984b520b1f1d48a22e7dd9f8d14a3a2
 * Libcrux: c03a2450e05a21ae0aa53a715add84a7b759c4f4
 */

#include "internal/libcrux_mlkem512_portable.h"

#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"

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
static Eurydice_arr_60 decapsulate_69(Eurydice_arr_7f0 *private_key,
                                      Eurydice_arr_56 *ciphertext) {
  return libcrux_ml_kem_ind_cca_decapsulate_620(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem512_portable_decapsulate(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext) {
  return decapsulate_69(private_key, ciphertext);
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
static tuple_17 encapsulate_35(Eurydice_arr_30 *public_key,
                               Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_ca0(public_key, randomness);
}

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_17 libcrux_ml_kem_mlkem512_portable_encapsulate(
    Eurydice_arr_30 *public_key, Eurydice_arr_60 randomness) {
  return encapsulate_35(public_key, &randomness);
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
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static libcrux_ml_kem_types_MlKemKeyPair_3e generate_keypair_9c(
    libcrux_sha3_Sha3_512Digest *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_150(randomness);
}

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_mlkem512_portable_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  return generate_keypair_9c(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key with const
generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
static KRML_MUSTINLINE bool validate_private_key_1c(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_fb(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key(
    Eurydice_arr_7f0 *private_key, Eurydice_arr_56 *ciphertext) {
  return validate_private_key_1c(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key_only with
const generics
- K= 2
- SECRET_KEY_SIZE= 1632
*/
static KRML_MUSTINLINE bool validate_private_key_only_49(
    Eurydice_arr_7f0 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_30(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key_only(
    Eurydice_arr_7f0 *private_key) {
  return validate_private_key_only_49(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE bool validate_public_key_49(
    Eurydice_arr_30 *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_64(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_public_key(
    Eurydice_arr_30 *public_key) {
  return validate_public_key_49(public_key);
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.decapsulate with const
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
static KRML_MUSTINLINE Eurydice_arr_60 decapsulate_690(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_56 *ciphertext) {
  return libcrux_ml_kem_ind_cca_unpacked_decapsulate_510(key_pair, ciphertext);
}

/**
 Decapsulate ML-KEM 512 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem512KeyPairUnpacked`] and an [`MlKem512Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem512_portable_unpacked_decapsulate(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *private_key,
    Eurydice_arr_56 *ciphertext) {
  return decapsulate_690(private_key, ciphertext);
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.encapsulate with const
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
static KRML_MUSTINLINE tuple_17 encapsulate_350(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
    Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_0c0(public_key,
                                                         randomness);
}

/**
 Encapsulate ML-KEM 512 (unpacked)

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an unpacked public key of type
 [`MlKem512PublicKeyUnpacked`], the SHA3-256 hash of this public key, and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_17 libcrux_ml_kem_mlkem512_portable_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
    Eurydice_arr_60 randomness) {
  return encapsulate_350(public_key, &randomness);
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.generate_keypair with
const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
static KRML_MUSTINLINE void generate_keypair_9c0(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *out) {
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_150(randomness, out);
}

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  generate_keypair_9c0(randomness, key_pair);
}

/**
 Generate ML-KEM 512 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_portable_unpacked_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked key_pair =
      libcrux_ml_kem_ind_cca_unpacked_default_7b_a0();
  libcrux_ml_kem_mlkem512_portable_unpacked_generate_key_pair_mut(randomness,
                                                                  &key_pair);
  return key_pair;
}

/**
 Create a new, empty unpacked key.
*/
libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_mlkem512_portable_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_7b_a0();
}

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
libcrux_ml_kem_mlkem512_portable_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_30_a0();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.keypair_from_private_key
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
*/
static KRML_MUSTINLINE void keypair_from_private_key_30(
    Eurydice_arr_7f0 *private_key,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_d1(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_from_private_mut(
    Eurydice_arr_7f0 *private_key,
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  keypair_from_private_key_30(private_key, key_pair);
}

/**
 Get the serialized private key.
*/
Eurydice_arr_7f0
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_6d(key_pair);
}

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_7f0 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_6d(key_pair,
                                                                   serialized);
}

/**
 Get the serialized public key.
*/
Eurydice_arr_30
libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked
        *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_64(key_pair);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem512_portable_unpacked_MlKem512KeyPairUnpacked *key_pair,
    Eurydice_arr_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_64(key_pair,
                                                                  serialized);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4 *public_key,
    Eurydice_arr_30 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_64(public_key, serialized);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.unpacked.unpack_public_key with
const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
static KRML_MUSTINLINE void unpack_public_key_1c(
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_73(public_key,
                                                       unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem512_portable_unpacked_unpacked_public_key(
    Eurydice_arr_30 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_d4
        *unpacked_public_key) {
  unpack_public_key_1c(public_key, unpacked_public_key);
}
