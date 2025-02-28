/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: a8f2211d1b95e0462a96382023b164a4116c7ca4
 * Eurydice: 788c5abefac3a9c7f79abae6a30fa8558e39764c
 * Karamel: 1d81d757d5d9e16dd6463ccc72324e587c707959
 * F*: b0961063393215ca65927f017720cb365a193833-dirty
 * Libcrux: bab611f6a9005751769f23d1d6cc3c7cf072c7e7
 */

#include "libcrux_mlkem768_portable.h"

#include "internal/libcrux_mlkem_portable.h"
#include "libcrux_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate with const generics
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
static void decapsulate_35(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_62(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
void libcrux_ml_kem_mlkem768_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]) {
  decapsulate_35(private_key, ciphertext, ret);
}

/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate with const generics
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
static tuple_c2 encapsulate_cd(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_ca(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_c2 libcrux_ml_kem_mlkem768_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key,
    uint8_t randomness[32U]) {
  return encapsulate_cd(public_key, randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem768_MlKem768KeyPair generate_keypair_ce(
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_15(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_mlkem768_portable_generate_key_pair(uint8_t randomness[64U]) {
  return generate_keypair_ce(randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key with const
generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool validate_private_key_31(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_37(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_portable_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext) {
  return validate_private_key_31(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key_only with
const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool validate_private_key_only_41(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_d6(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_portable_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_d9 *private_key) {
  return validate_private_key_only_41(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool validate_public_key_41(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_89(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem768_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_30 *public_key) {
  return validate_public_key_41(public_key->value);
}
