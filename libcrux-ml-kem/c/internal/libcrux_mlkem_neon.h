/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 150afa5f6ba469c99c4a2fa6e1037ae5a4004c68
 * Eurydice: ec7dfaf71369de6c7ab306a7ada725b6fc004a33
 * Karamel: 254e099bd586b17461845f6b0cab44c3ef5080e9
 * F*: 7b347386330d0e5a331a220535b6f15288903234
 * Libcrux: 23ba8451a39d29970cc274e93bb0b2fe91fbc040
 */


#ifndef internal_libcrux_mlkem_neon_H
#define internal_libcrux_mlkem_neon_H

#include "eurydice_glue.h"


#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_core.h"
#include "../libcrux_mlkem_neon.h"

/**
A monomorphic instance of Eurydice.arr
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_f9_s
{ libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector data[16U]; }
Eurydice_arr_f9;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_f30_s { Eurydice_arr_f9 data[2U]; } Eurydice_arr_f30;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$2size_t]]
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_e21_s { Eurydice_arr_f30 data[2U]; } Eurydice_arr_e21;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d_s
{
  Eurydice_arr_f30 t_as_ntt;
  Eurydice_arr_60 seed_for_A;
  Eurydice_arr_e21 A;
}
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d_s
{
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_7d ind_cpa_public_key;
  Eurydice_arr_60 public_key_hash;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d;

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- T_AS_NTT_ENCODED_SIZE= 768
- PUBLIC_KEY_SIZE= 800
*/
void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e1(
  Eurydice_arr_30 *public_key,
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *unpacked_public_key
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $2size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_7d_s
{
  Eurydice_arr_f30 ind_cpa_private_key;
  Eurydice_arr_60 implicit_rejection_value;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_7d;

typedef struct libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked_s
{
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_7d private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d public_key;
}
libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked;

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_37(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *self,
  Eurydice_arr_30 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_37(
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self,
  Eurydice_arr_30 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_30
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_37(
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_90(
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self,
  Eurydice_arr_7f0 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
*/
Eurydice_arr_7f0
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_90(
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *self
);

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CPA_SECRET_KEY_SIZE= 768
- PUBLIC_KEY_SIZE= 800
- T_AS_NTT_ENCODED_SIZE= 768
*/
void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_c2(
  Eurydice_arr_7f0 *private_key,
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair
);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d
libcrux_ml_kem_ind_cca_unpacked_default_30_e3(void);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
*/
libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_e3(void);

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
void
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_581(
  libcrux_sha3_Sha3_512Digest randomness,
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *out
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
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
tuple_17
libcrux_ml_kem_ind_cca_unpacked_encapsulate_551(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_7d *public_key,
  Eurydice_arr_60 *randomness
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa1(
  libcrux_ml_kem_mlkem512_neon_unpacked_MlKem512KeyPairUnpacked *key_pair,
  Eurydice_arr_56 *ciphertext
);

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 2
- PUBLIC_KEY_SIZE= 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_37(Eurydice_arr_30 *public_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_c1(Eurydice_arr_7f0 *private_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 2
- SECRET_KEY_SIZE= 1632
- CIPHERTEXT_SIZE= 768
*/
bool
libcrux_ml_kem_ind_cca_validate_private_key_ac(
  Eurydice_arr_7f0 *private_key,
  Eurydice_arr_56 *_ciphertext
);

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 2
- CPA_PRIVATE_KEY_SIZE= 768
- PRIVATE_KEY_SIZE= 1632
- PUBLIC_KEY_SIZE= 800
- ETA1= 3
- ETA1_RANDOMNESS_SIZE= 192
*/
libcrux_ml_kem_types_MlKemKeyPair_3e
libcrux_ml_kem_ind_cca_generate_keypair_581(libcrux_sha3_Sha3_512Digest *randomness);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
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
tuple_17
libcrux_ml_kem_ind_cca_encapsulate_991(
  Eurydice_arr_30 *public_key,
  Eurydice_arr_60 *randomness
);

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_decapsulate_761(
  Eurydice_arr_7f0 *private_key,
  Eurydice_arr_56 *ciphertext
);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_fe0_s { Eurydice_arr_f9 data[3U]; } Eurydice_arr_fe0;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$3size_t]]
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_aa0_s { Eurydice_arr_fe0 data[3U]; } Eurydice_arr_aa0;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec_s
{
  Eurydice_arr_fe0 t_as_ntt;
  Eurydice_arr_60 seed_for_A;
  Eurydice_arr_aa0 A;
}
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec_s
{
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_ec ind_cpa_public_key;
  Eurydice_arr_60 public_key_hash;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec;

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- T_AS_NTT_ENCODED_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e0(
  Eurydice_arr_74 *public_key,
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *unpacked_public_key
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $3size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ec_s
{
  Eurydice_arr_fe0 ind_cpa_private_key;
  Eurydice_arr_60 implicit_rejection_value;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ec;

typedef struct libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked_s
{
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_ec private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec public_key;
}
libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked;

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.public_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
*libcrux_ml_kem_ind_cca_unpacked_public_key_11_a5(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self
);

/**
This function found in impl {core::clone::Clone for libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@2]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.clone_d7
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
libcrux_ml_kem_ind_cca_unpacked_clone_d7_a5(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *self
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_21(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *self,
  Eurydice_arr_74 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_21(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self,
  Eurydice_arr_74 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_74
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_21(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_b0(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self,
  Eurydice_arr_ea *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_arr_ea
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_b0(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *self
);

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
*/
void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_36(
  Eurydice_arr_ea *private_key,
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair
);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec
libcrux_ml_kem_ind_cca_unpacked_default_30_a5(void);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
*/
libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_a5(void);

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_580(
  libcrux_sha3_Sha3_512Digest randomness,
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *out
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
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
tuple_56
libcrux_ml_kem_ind_cca_unpacked_encapsulate_550(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_ec *public_key,
  Eurydice_arr_60 *randomness
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa0(
  libcrux_ml_kem_mlkem768_neon_unpacked_MlKem768KeyPairUnpacked *key_pair,
  Eurydice_arr_2c *ciphertext
);

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_21(Eurydice_arr_74 *public_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_20(Eurydice_arr_ea *private_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool
libcrux_ml_kem_ind_cca_validate_private_key_a5(
  Eurydice_arr_ea *private_key,
  Eurydice_arr_2c *_ciphertext
);

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 3
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_580(libcrux_sha3_Sha3_512Digest *randomness);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
tuple_56
libcrux_ml_kem_ind_cca_encapsulate_990(
  Eurydice_arr_74 *public_key,
  Eurydice_arr_60 *randomness
);

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_decapsulate_760(
  Eurydice_arr_ea *private_key,
  Eurydice_arr_2c *ciphertext
);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_7f_s { Eurydice_arr_f9 data[4U]; } Eurydice_arr_7f;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr libcrux_ml_kem_polynomial_PolynomialRingElement libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector[[$4size_t]]
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_95_s { Eurydice_arr_7f data[4U]; } Eurydice_arr_95;

/**
A monomorphic instance of libcrux_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56_s
{
  Eurydice_arr_7f t_as_ntt;
  Eurydice_arr_60 seed_for_A;
  Eurydice_arr_95 A;
}
libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56;

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPublicKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56_s
{
  libcrux_ml_kem_ind_cpa_unpacked_IndCpaPublicKeyUnpacked_56 ind_cpa_public_key;
  Eurydice_arr_60 public_key_hash;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56;

/**
 Generate an unpacked key from a serialized key.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.unpack_public_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- T_AS_NTT_ENCODED_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
void
libcrux_ml_kem_ind_cca_unpacked_unpack_public_key_5e(
  Eurydice_arr_00 *public_key,
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *unpacked_public_key
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.MlKemPrivateKeyUnpacked
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- $4size_t
*/
typedef struct libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_56_s
{
  Eurydice_arr_7f ind_cpa_private_key;
  Eurydice_arr_60 implicit_rejection_value;
}
libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_56;

typedef struct libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked_s
{
  libcrux_ml_kem_ind_cca_unpacked_MlKemPrivateKeyUnpacked_56 private_key;
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 public_key;
}
libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked;

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_mut_dd
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_mut_dd_a1(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *self,
  Eurydice_arr_00 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_mut_11_a1(
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self,
  Eurydice_arr_00 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_public_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_00
libcrux_ml_kem_ind_cca_unpacked_serialized_public_key_11_a1(
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_mut_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
void
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_mut_11_fd(
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self,
  Eurydice_arr_17 *serialized
);

/**
This function found in impl {libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.serialized_private_key_11
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_arr_17
libcrux_ml_kem_ind_cca_unpacked_serialized_private_key_11_fd(
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *self
);

/**
 Take a serialized private key and generate an unpacked key pair from it.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.keys_from_private_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
*/
void
libcrux_ml_kem_ind_cca_unpacked_keys_from_private_key_21(
  Eurydice_arr_17 *private_key,
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *key_pair
);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemPublicKeyUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_30
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56
libcrux_ml_kem_ind_cca_unpacked_default_30_40(void);

/**
This function found in impl {core::default::Default for libcrux_ml_kem::ind_cca::unpacked::MlKemKeyPairUnpacked<Vector, K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.default_7b
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
*/
libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked
libcrux_ml_kem_ind_cca_unpacked_default_7b_40(void);

/**
 Generate Unpacked Keys
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
void
libcrux_ml_kem_ind_cca_unpacked_generate_keypair_58(
  libcrux_sha3_Sha3_512Digest randomness,
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *out
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
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
tuple_2b
libcrux_ml_kem_ind_cca_unpacked_encapsulate_55(
  libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked_56 *public_key,
  Eurydice_arr_60 *randomness
);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.unpacked.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_unpacked_decapsulate_aa(
  libcrux_ml_kem_mlkem1024_neon_unpacked_MlKem1024KeyPairUnpacked *key_pair,
  Eurydice_arr_00 *ciphertext
);

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_a1(Eurydice_arr_00 *public_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key_only
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_ml_kem_ind_cca_validate_private_key_only_1f(Eurydice_arr_17 *private_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_private_key
with types libcrux_ml_kem_hash_functions_neon_Simd128Hash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool
libcrux_ml_kem_ind_cca_validate_private_key_ba(
  Eurydice_arr_17 *private_key,
  Eurydice_arr_00 *_ciphertext
);

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
with const generics
- K= 4
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_58(libcrux_sha3_Sha3_512Digest *randomness);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
tuple_2b
libcrux_ml_kem_ind_cca_encapsulate_99(Eurydice_arr_00 *public_key, Eurydice_arr_60 *randomness);

/**
 This code verifies on some machines, runs out of memory on others
*/
/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate
with types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector, libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_variant_MlKem
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
Eurydice_arr_60
libcrux_ml_kem_ind_cca_decapsulate_76(
  Eurydice_arr_17 *private_key,
  Eurydice_arr_00 *ciphertext
);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_mlkem_neon_H_DEFINED
#endif /* internal_libcrux_mlkem_neon_H */
