/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: bb62a9b39db4ea8c6d536fe61b7d26663751bf3c
 * Eurydice: 46cef5d58a855ed049fa89bfe99c959b5d9d0d4b
 * Karamel: 39cb85a718da8ae4a724d31b08f9134ca9311336
 * F*: 71d8221589d4d438af3706d89cb653cf53e18aab
 * Libcrux: d5c2e3173d83715a5459e13c74734f9df866b57f
 */

#include "libcrux_mlkem512_portable.h"

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
static void decapsulate_69(libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
                           libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext,
                           uint8_t ret[32U]) {
  libcrux_ml_kem_ind_cca_decapsulate_620(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 512

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem512PrivateKey`] and an
 [`MlKem512Ciphertext`].
*/
void libcrux_ml_kem_mlkem512_portable_decapsulate(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext, uint8_t ret[32U]) {
  decapsulate_69(private_key, ciphertext, ret);
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
static tuple_41 encapsulate_35(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key, uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_encapsulate_ca0(public_key, randomness);
}

/**
 Encapsulate ML-KEM 512

 Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_41 libcrux_ml_kem_mlkem512_portable_encapsulate(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key,
    uint8_t randomness[32U]) {
  return encapsulate_35(public_key, randomness);
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
    uint8_t *randomness) {
  return libcrux_ml_kem_ind_cca_generate_keypair_150(randomness);
}

/**
 Generate ML-KEM 512 Key Pair
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_mlkem512_portable_generate_key_pair(uint8_t randomness[64U]) {
  return generate_keypair_9c(randomness);
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
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext) {
  return libcrux_ml_kem_ind_cca_validate_private_key_fb(private_key,
                                                        ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key,
    libcrux_ml_kem_types_MlKemCiphertext_1a *ciphertext) {
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
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key) {
  return libcrux_ml_kem_ind_cca_validate_private_key_only_30(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_private_key_only(
    libcrux_ml_kem_types_MlKemPrivateKey_fa *private_key) {
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
static KRML_MUSTINLINE bool validate_public_key_49(uint8_t *public_key) {
  return libcrux_ml_kem_ind_cca_validate_public_key_64(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_ml_kem_mlkem512_portable_validate_public_key(
    libcrux_ml_kem_types_MlKemPublicKey_52 *public_key) {
  return validate_public_key_49(public_key->value);
}
