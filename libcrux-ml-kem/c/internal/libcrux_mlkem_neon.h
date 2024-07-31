/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 45b95e0f63cb830202c0b3ca00a341a3451a02ba
 * Eurydice: 013beb9e4046a151131c6a56dfe25e606b49c4a1
 * Karamel: 4626e5fcb3787a47c806d160539342ade4b0809c
 * F*: b2931dfbe46e839cd757220c63d48c71335bb1ae
 * Libcrux: a0db75c27aa09b79eae1c2315196383465857308
 */

#ifndef __internal_libcrux_mlkem_neon_H
#define __internal_libcrux_mlkem_neon_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_mlkem_neon.h"
#include "eurydice_glue.h"
#include "internal/libcrux_core.h"
#include "internal/libcrux_mlkem_portable.h"

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector and with const generics:
- K = 2
- RANKED_BYTES_PER_RING_ELEMENT = 768
- PUBLIC_KEY_SIZE = 800
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_41(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__2size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_32(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
*/
libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_ind_cca_generate_keypair_32(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 2
- CIPHERTEXT_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_32(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__2size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 2
- CIPHERTEXT_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_24(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 2
- SECRET_KEY_SIZE = 1632
- CPA_SECRET_KEY_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- CIPHERTEXT_SIZE = 768
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 800
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_32(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__2size_t
        *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 2
- SECRET_KEY_SIZE = 1632
- CPA_SECRET_KEY_SIZE = 768
- PUBLIC_KEY_SIZE = 800
- CIPHERTEXT_SIZE = 768
- T_AS_NTT_ENCODED_SIZE = 768
- C1_SIZE = 640
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 800
*/
void libcrux_ml_kem_ind_cca_decapsulate_24(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector and with const generics:
- K = 3
- RANKED_BYTES_PER_RING_ELEMENT = 1152
- PUBLIC_KEY_SIZE = 1184
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_62(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 3
- CPA_PRIVATE_KEY_SIZE = 1152
- PRIVATE_KEY_SIZE = 2400
- PUBLIC_KEY_SIZE = 1184
- BYTES_PER_RING_ELEMENT = 1152
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__3size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_d7(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 3
- CPA_PRIVATE_KEY_SIZE = 1152
- PRIVATE_KEY_SIZE = 2400
- PUBLIC_KEY_SIZE = 1184
- BYTES_PER_RING_ELEMENT = 1152
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_d7(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 3
- CIPHERTEXT_SIZE = 1088
- PUBLIC_KEY_SIZE = 1184
- T_AS_NTT_ENCODED_SIZE = 1152
- C1_SIZE = 960
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_d7(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__3size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 3
- CIPHERTEXT_SIZE = 1088
- PUBLIC_KEY_SIZE = 1184
- T_AS_NTT_ENCODED_SIZE = 1152
- C1_SIZE = 960
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- VECTOR_U_BLOCK_LEN = 320
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_40(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 3
- SECRET_KEY_SIZE = 2400
- CPA_SECRET_KEY_SIZE = 1152
- PUBLIC_KEY_SIZE = 1184
- CIPHERTEXT_SIZE = 1088
- T_AS_NTT_ENCODED_SIZE = 1152
- C1_SIZE = 960
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1120
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_d7(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__3size_t
        *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 3
- SECRET_KEY_SIZE = 2400
- CPA_SECRET_KEY_SIZE = 1152
- PUBLIC_KEY_SIZE = 1184
- CIPHERTEXT_SIZE = 1088
- T_AS_NTT_ENCODED_SIZE = 1152
- C1_SIZE = 960
- C2_SIZE = 128
- VECTOR_U_COMPRESSION_FACTOR = 10
- VECTOR_V_COMPRESSION_FACTOR = 4
- C1_BLOCK_SIZE = 320
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1120
*/
void libcrux_ml_kem_ind_cca_decapsulate_40(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector and with const generics:
- K = 4
- RANKED_BYTES_PER_RING_ELEMENT = 1536
- PUBLIC_KEY_SIZE = 1568
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_ae(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__4size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_91(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_91(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 4
- CIPHERTEXT_SIZE = 1568
- PUBLIC_KEY_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- VECTOR_U_BLOCK_LEN = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_91(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__4size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 4
- CIPHERTEXT_SIZE = 1568
- PUBLIC_KEY_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- VECTOR_U_BLOCK_LEN = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_51(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash and with const generics:
- K = 4
- SECRET_KEY_SIZE = 3168
- CPA_SECRET_KEY_SIZE = 1536
- PUBLIC_KEY_SIZE = 1568
- CIPHERTEXT_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- C1_BLOCK_SIZE = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1600
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_91(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector__4size_t
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_neon_vector_type_SIMD128Vector,
libcrux_ml_kem_hash_functions_neon_Simd128Hash, libcrux_ml_kem_ind_cca_MlKem and
with const generics:
- K = 4
- SECRET_KEY_SIZE = 3168
- CPA_SECRET_KEY_SIZE = 1536
- PUBLIC_KEY_SIZE = 1568
- CIPHERTEXT_SIZE = 1568
- T_AS_NTT_ENCODED_SIZE = 1536
- C1_SIZE = 1408
- C2_SIZE = 160
- VECTOR_U_COMPRESSION_FACTOR = 11
- VECTOR_V_COMPRESSION_FACTOR = 5
- C1_BLOCK_SIZE = 352
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
- ETA2 = 2
- ETA2_RANDOMNESS_SIZE = 128
- IMPLICIT_REJECTION_HASH_INPUT_SIZE = 1600
*/
void libcrux_ml_kem_ind_cca_decapsulate_51(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_mlkem_neon_H_DEFINED
#endif
