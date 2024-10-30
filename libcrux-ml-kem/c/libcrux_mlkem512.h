/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 2b71c3c42337fe17ceca860bedaafb3443e6c5e8
 * Eurydice: dcfae68c874635956f71d4c05928841b29ad0a8b
 * Karamel: 87384b244a98a0c41a2e14c65b872d885af7c8df
 * F*: 8b6fce63ca91b16386d8f76e82ea87a3c109a208
 * Libcrux: 4b0d78759e0adf160bab80862883bd5ba7338977
 */

#ifndef __libcrux_mlkem512_H
#define __libcrux_mlkem512_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue.h"
#include "libcrux_core.h"

#define LIBCRUX_ML_KEM_MLKEM512_C1_BLOCK_SIZE_512 ((size_t)320U)

#define LIBCRUX_ML_KEM_MLKEM512_C1_SIZE_512 ((size_t)640U)

#define LIBCRUX_ML_KEM_MLKEM512_C2_SIZE_512 ((size_t)128U)

#define LIBCRUX_ML_KEM_MLKEM512_CPA_PKE_CIPHERTEXT_SIZE_512 ((size_t)768U)

#define LIBCRUX_ML_KEM_MLKEM512_CPA_PKE_PUBLIC_KEY_SIZE_512 ((size_t)800U)

#define LIBCRUX_ML_KEM_MLKEM512_CPA_PKE_SECRET_KEY_SIZE_512 ((size_t)768U)

#define LIBCRUX_ML_KEM_MLKEM512_ETA1 ((size_t)3U)

#define LIBCRUX_ML_KEM_MLKEM512_ETA1_RANDOMNESS_SIZE ((size_t)192U)

#define LIBCRUX_ML_KEM_MLKEM512_ETA2 ((size_t)2U)

#define LIBCRUX_ML_KEM_MLKEM512_ETA2_RANDOMNESS_SIZE ((size_t)128U)

#define LIBCRUX_ML_KEM_MLKEM512_IMPLICIT_REJECTION_HASH_INPUT_SIZE \
  ((size_t)800U)

typedef libcrux_ml_kem_types_MlKemCiphertext_1a
    libcrux_ml_kem_mlkem512_MlKem512Ciphertext;

typedef libcrux_ml_kem_types_MlKemKeyPair_3e
    libcrux_ml_kem_mlkem512_MlKem512KeyPair;

typedef libcrux_ml_kem_types_MlKemPrivateKey_fa
    libcrux_ml_kem_mlkem512_MlKem512PrivateKey;

typedef libcrux_ml_kem_types_MlKemPublicKey_52
    libcrux_ml_kem_mlkem512_MlKem512PublicKey;

#define LIBCRUX_ML_KEM_MLKEM512_RANKED_BYTES_PER_RING_ELEMENT_512 ((size_t)768U)

#define LIBCRUX_ML_KEM_MLKEM512_RANK_512 ((size_t)2U)

#define LIBCRUX_ML_KEM_MLKEM512_SECRET_KEY_SIZE_512 ((size_t)1632U)

#define LIBCRUX_ML_KEM_MLKEM512_T_AS_NTT_ENCODED_SIZE_512 ((size_t)768U)

#define LIBCRUX_ML_KEM_MLKEM512_VECTOR_U_COMPRESSION_FACTOR_512 ((size_t)10U)

#define LIBCRUX_ML_KEM_MLKEM512_VECTOR_V_COMPRESSION_FACTOR_512 ((size_t)4U)

#if defined(__cplusplus)
}
#endif

#define __libcrux_mlkem512_H_DEFINED
#endif
