/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: 9664988fc6405409f3815686f7284fb32e8d9b8e
 * Karamel: 80f5435f2fc505973c469a4afcc8d875cddd0d8b
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: 1746ced6ccd3e8d73185d7aee13af229426b7b7a
 */

#include "internal/libcrux_mlkem1024_avx2.h"

#include "internal/libcrux_mlkem_avx2.h"
#include "libcrux_core.h"

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.decapsulate_avx2 with const generics
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
static Eurydice_arr_60 decapsulate_avx2_e0(Eurydice_arr_17 *private_key,
                                           Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_decapsulate_a10(private_key, ciphertext);
}

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
static Eurydice_arr_60 decapsulate_e0(Eurydice_arr_17 *private_key,
                                      Eurydice_arr_00 *ciphertext) {
  return decapsulate_avx2_e0(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem1024_avx2_decapsulate(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  return decapsulate_e0(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.encapsulate_avx2 with const generics
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
static tuple_2b encapsulate_avx2_8f(Eurydice_arr_00 *public_key,
                                    Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_700(public_key, randomness);
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
static tuple_2b encapsulate_8f(Eurydice_arr_00 *public_key,
                               Eurydice_arr_60 *randomness) {
  return encapsulate_avx2_8f(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_2b libcrux_ml_kem_mlkem1024_avx2_encapsulate(Eurydice_arr_00 *public_key,
                                                   Eurydice_arr_60 randomness) {
  return encapsulate_8f(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair_avx2 with const
generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_avx2_b4(
    libcrux_sha3_Sha3_512Digest *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_bb0(randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.generate_keypair with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_b4(
    libcrux_sha3_Sha3_512Digest *randomness) {
  return generate_keypair_avx2_b4(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_avx2_generate_key_pair(
    libcrux_sha3_Sha3_512Digest randomness) {
  return generate_keypair_b4(&randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key_avx2 with const
generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static bool validate_private_key_avx2_6b(Eurydice_arr_17 *private_key,
                                         Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_b9(private_key,
                                                        ciphertext);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key with const
generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static bool validate_private_key_6b(Eurydice_arr_17 *private_key,
                                    Eurydice_arr_00 *ciphertext) {
  return validate_private_key_avx2_6b(private_key, ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_avx2_validate_private_key(
    Eurydice_arr_17 *private_key, Eurydice_arr_00 *ciphertext) {
  return validate_private_key_6b(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_private_key_only with const
generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
static KRML_MUSTINLINE bool validate_private_key_only_44(
    Eurydice_arr_17 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_5e(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_avx2_validate_private_key_only(
    Eurydice_arr_17 *private_key) {
  return validate_private_key_only_44(private_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key_avx2 with const
generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static bool validate_public_key_avx2_44(Eurydice_arr_00 *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_78(public_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.validate_public_key with const
generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static bool validate_public_key_44(Eurydice_arr_00 *public_key) {
  return validate_public_key_avx2_44(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem1024_avx2_validate_public_key(
    Eurydice_arr_00 *public_key) {
  return validate_public_key_44(public_key);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.decapsulate_avx2 with const
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
static Eurydice_arr_60 decapsulate_avx2_e00(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *ciphertext) {
  return libcrux_ml_kem_ind_cca_unpacked_decapsulate_120(key_pair, ciphertext);
}

/**
 Unpacked decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.decapsulate with const
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
static Eurydice_arr_60 decapsulate_e00(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *ciphertext) {
  return decapsulate_avx2_e00(key_pair, ciphertext);
}

/**
 Decapsulate ML-KEM 1024 (unpacked)

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an unpacked key pair of type
 [`MlKem1024KeyPairUnpacked`] and an [`MlKem1024Ciphertext`].
*/
Eurydice_arr_60 libcrux_ml_kem_mlkem1024_avx2_unpacked_decapsulate(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
        *private_key,
    Eurydice_arr_00 *ciphertext) {
  return decapsulate_e00(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.encapsulate_avx2 with const
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
static tuple_2b encapsulate_avx2_8f0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_60 *randomness) {
  return libcrux_ml_kem_ind_cca_unpacked_encapsulate_700(public_key,
                                                         randomness);
}

/**
 Unpacked encapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.encapsulate with const
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
static tuple_2b encapsulate_8f0(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_60 *randomness) {
  return encapsulate_avx2_8f0(public_key, randomness);
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
tuple_2b libcrux_ml_kem_mlkem1024_avx2_unpacked_encapsulate(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_60 randomness) {
  return encapsulate_8f0(public_key, &randomness);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.generate_keypair_avx2 with
const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void generate_keypair_avx2_b40(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *out) {
  libcrux_ml_kem_ind_cca_unpacked_generate_keypair_bb0(randomness, out);
}

/**
 Generate a key pair
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.generate_keypair with const
generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static void generate_keypair_b40(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *out) {
  generate_keypair_avx2_b40(randomness, out);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_generate_key_pair_mut(
    libcrux_sha3_Sha3_512Digest randomness,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  generate_keypair_b40(randomness, key_pair);
}

/**
 Generate ML-KEM 1024 Key Pair in "unpacked" form.
*/
libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
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
libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_mlkem1024_avx2_unpacked_init_key_pair(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_7b_42();
}

/**
 Create a new, empty unpacked public key.
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
libcrux_ml_kem_mlkem1024_avx2_unpacked_init_public_key(void) {
  return libcrux_ml_kem_ind_cca_unpacked_default_30_42();
}

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.keypair_from_private_key
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
static KRML_MUSTINLINE void keypair_from_private_key_b4(
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_37(private_key,
                                                           key_pair);
}

/**
 Get an unpacked key from a private key.
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_from_private_mut(
    Eurydice_arr_17 *private_key,
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  keypair_from_private_key_b4(private_key, key_pair);
}

/**
 Get the serialized private key.
*/
Eurydice_arr_17
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_private_key(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_c9(key_pair);
}

/**
 Get the serialized private key.
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_private_key_mut(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_17 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_c9(key_pair,
                                                                   serialized);
}

/**
 Get the serialized public key.
*/
Eurydice_arr_00
libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_public_key(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair) {
  return libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_78(key_pair);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_key_pair_serialized_public_key_mut(
    libcrux_ml_kem_mlkem1024_avx2_unpacked_MlKem1024KeyPairUnpacked *key_pair,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_78(key_pair,
                                                                  serialized);
}

/**
 Get the serialized public key.
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_serialized_public_key(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39 *public_key,
    Eurydice_arr_00 *serialized) {
  libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_78(public_key, serialized);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.unpack_public_key_avx2 with
const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static void unpack_public_key_avx2_6b(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
        *unpacked_public_key) {
  libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_fb0(public_key,
                                                        unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.avx2.unpacked.unpack_public_key with const
generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static void unpack_public_key_6b(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
        *unpacked_public_key) {
  unpack_public_key_avx2_6b(public_key, unpacked_public_key);
}

/**
 Get the unpacked public key.
*/
void libcrux_ml_kem_mlkem1024_avx2_unpacked_unpacked_public_key(
    Eurydice_arr_00 *public_key,
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_39
        *unpacked_public_key) {
  unpack_public_key_6b(public_key, unpacked_public_key);
}
