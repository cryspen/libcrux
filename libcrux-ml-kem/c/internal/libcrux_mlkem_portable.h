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
 * Libcrux: 8a3c1c4c84f258580d53bfef5ad2b1b7d5ef5fca
 */

#ifndef __internal_libcrux_mlkem_portable_H
#define __internal_libcrux_mlkem_portable_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_mlkem_portable.h"
#include "eurydice_glue.h"
#include "internal/libcrux_core.h"
#include "internal/libcrux_sha3_internal.h"

extern const int16_t libcrux_ml_kem_polynomial_ZETAS_TIMES_MONTGOMERY_R[128U];

#define LIBCRUX_ML_KEM_POLYNOMIAL_VECTORS_IN_RING_ELEMENT  \
  (LIBCRUX_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / \
   LIBCRUX_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR)

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector and with const
generics:
- K = 4
- RANKED_BYTES_PER_RING_ELEMENT = 1536
- PUBLIC_KEY_SIZE = 1568
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_38(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] and with const
generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_23(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] and with const
generics:
- K = 4
- CPA_PRIVATE_KEY_SIZE = 1536
- PRIVATE_KEY_SIZE = 3168
- PUBLIC_KEY_SIZE = 1568
- BYTES_PER_RING_ELEMENT = 1536
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_mlkem1024_MlKem1024KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_23(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_23(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1568size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_12(
    libcrux_ml_kem_types_MlKemPublicKey____1568size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_23(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__4size_t
        *key_pair,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$4size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_12(
    libcrux_ml_kem_types_MlKemPrivateKey____3168size_t *private_key,
    libcrux_ml_kem_mlkem1024_MlKem1024Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector and with const
generics:
- K = 2
- RANKED_BYTES_PER_RING_ELEMENT = 768
- PUBLIC_KEY_SIZE = 800
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_6b(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] and with const
generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_60(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] and with const
generics:
- K = 2
- CPA_PRIVATE_KEY_SIZE = 768
- PRIVATE_KEY_SIZE = 1632
- PUBLIC_KEY_SIZE = 800
- BYTES_PER_RING_ELEMENT = 768
- ETA1 = 3
- ETA1_RANDOMNESS_SIZE = 192
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_types_MlKemKeyPair____1632size_t__800size_t
libcrux_ml_kem_ind_cca_generate_keypair_60(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_60(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___768size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_8f(
    libcrux_ml_kem_types_MlKemPublicKey____800size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_60(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__2size_t
        *key_pair,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$2size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_8f(
    libcrux_ml_kem_types_MlKemPrivateKey____1632size_t *private_key,
    libcrux_ml_kem_types_MlKemCiphertext____768size_t *ciphertext,
    uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.validate_public_key with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector and with const
generics:
- K = 3
- RANKED_BYTES_PER_RING_ELEMENT = 1152
- PUBLIC_KEY_SIZE = 1184
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
bool libcrux_ml_kem_ind_cca_validate_public_key_1e(uint8_t *public_key);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair_unpacked with
types libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] and with const
generics:
- K = 3
- CPA_PRIVATE_KEY_SIZE = 1152
- PRIVATE_KEY_SIZE = 2400
- PUBLIC_KEY_SIZE = 1184
- BYTES_PER_RING_ELEMENT = 1152
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__3size_t
libcrux_ml_kem_ind_cca_generate_keypair_unpacked_80(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.generate_keypair with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] and with const
generics:
- K = 3
- CPA_PRIVATE_KEY_SIZE = 1152
- PRIVATE_KEY_SIZE = 2400
- PUBLIC_KEY_SIZE = 1184
- BYTES_PER_RING_ELEMENT = 1152
- ETA1 = 2
- ETA1_RANDOMNESS_SIZE = 128
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
libcrux_ml_kem_mlkem768_MlKem768KeyPair
libcrux_ml_kem_ind_cca_generate_keypair_80(uint8_t randomness[64U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_unpacked_80(
    libcrux_ml_kem_ind_cca_unpacked_MlKemPublicKeyUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__3size_t
        *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.encapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_
libcrux_ml_kem_ind_cca_encapsulate_c3(
    libcrux_ml_kem_types_MlKemPublicKey____1184size_t *public_key,
    uint8_t randomness[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate_unpacked with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]] and with const
generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_unpacked_80(
    libcrux_ml_kem_ind_cca_unpacked_MlKemKeyPairUnpacked__libcrux_ml_kem_vector_portable_vector_type_PortableVector__3size_t
        *key_pair,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

/**
A monomorphic instance of libcrux_ml_kem.ind_cca.decapsulate with types
libcrux_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_ml_kem_hash_functions_portable_PortableHash[[$3size_t]],
libcrux_ml_kem_ind_cca_MlKem and with const generics:
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
Furthermore, this instances features the following traits:
- {(libcrux_ml_kem::ind_cca::Variant for libcrux_ml_kem::ind_cca::MlKem)}
- {(libcrux_ml_kem::vector::traits::Operations for
libcrux_ml_kem::vector::portable::vector_type::PortableVector)}
*/
void libcrux_ml_kem_ind_cca_decapsulate_c3(
    libcrux_ml_kem_types_MlKemPrivateKey____2400size_t *private_key,
    libcrux_ml_kem_mlkem768_MlKem768Ciphertext *ciphertext, uint8_t ret[32U]);

#if defined(__cplusplus)
}
#endif

#define __internal_libcrux_mlkem_portable_H_DEFINED
#endif
