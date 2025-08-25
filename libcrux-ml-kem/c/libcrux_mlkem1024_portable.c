/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 5807deab3f588567f00046b8ee83e4eba7cff5f6
 * Eurydice: 924e44f2e6e8caac37cddca618ba9488f0990ccc
 * Karamel: c56e0932f05c89c8c68089d909ad9c195f44a02c
 * F*: 0c4b790fd608bccfc332d3ff1e9b29c9be8b0595
 * Libcrux: 85ef3af5e4511668b215821a564d6537be61d44c
 */


#include "libcrux_mlkem1024_portable.h"

#include "libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.decapsulate
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
static void
decapsulate_e0(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext,
  uint8_t ret[32U]
)
{
  libcrux_ml_kem_ind_cca_decapsulate_621(private_key, ciphertext, ret);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
*/
void
libcrux_ml_kem_mlkem1024_portable_decapsulate(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext,
  uint8_t ret[32U]
)
{
  decapsulate_e0(private_key, ciphertext, ret);
}

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.encapsulate
with const generics
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
static tuple_fa
encapsulate_8f(libcrux_ml_kem_types_MlKemPublicKey_64 *public_key, uint8_t *randomness)
{
  return libcrux_ml_kem_ind_cca_encapsulate_ca1(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_fa
libcrux_ml_kem_mlkem1024_portable_encapsulate(
  libcrux_ml_kem_types_MlKemPublicKey_64 *public_key,
  uint8_t randomness[32U]
)
{
  return encapsulate_8f(public_key, randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.generate_keypair
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
static libcrux_ml_kem_mlkem1024_MlKem1024KeyPair generate_keypair_b4(uint8_t *randomness)
{
  return libcrux_ml_kem_ind_cca_generate_keypair_151(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_mlkem1024_portable_generate_key_pair(uint8_t randomness[64U])
{
  return generate_keypair_b4(randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE bool
validate_private_key_6b(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext
)
{
  return libcrux_ml_kem_ind_cca_validate_private_key_b5(private_key, ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_portable_validate_private_key(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key,
  libcrux_ml_kem_types_MlKemCiphertext_64 *ciphertext
)
{
  return validate_private_key_6b(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.validate_private_key_only
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
static KRML_MUSTINLINE bool
validate_private_key_only_44(libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key)
{
  return libcrux_ml_kem_ind_cca_validate_private_key_only_60(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_portable_validate_private_key_only(
  libcrux_ml_kem_types_MlKemPrivateKey_83 *private_key
)
{
  return validate_private_key_only_44(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.instantiations.portable.validate_public_key
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_public_key_44(uint8_t *public_key)
{
  return libcrux_ml_kem_ind_cca_validate_public_key_ff(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool
libcrux_ml_kem_mlkem1024_portable_validate_public_key(
  libcrux_ml_kem_types_MlKemPublicKey_64 *public_key
)
{
  return validate_public_key_44(public_key->value);
}

