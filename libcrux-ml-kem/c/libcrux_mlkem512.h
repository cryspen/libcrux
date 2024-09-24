/*
 * SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: 28d543bfacc902ba9cc2a734b76baae9583892a4
 * Eurydice: 1a65dbf3758fe310833718c645a64266294a29ac
 * Karamel: 15d4bce74a2d43e34a64f48f8311b7d9bcb0e152
 * F*: 5643e656b989aca7629723653a2570c7df6252b9-dirty
 * Libcrux: 2cc5d08dc51d9011b73e45fa933da711162d0d01
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

typedef libcrux_ml_kem_types_MlKemCiphertext_e8
    libcrux_ml_kem_mlkem512_MlKem512Ciphertext;

typedef libcrux_ml_kem_types_MlKemKeyPair_cb
    libcrux_ml_kem_mlkem512_MlKem512KeyPair;

typedef libcrux_ml_kem_types_MlKemPrivateKey_5e
    libcrux_ml_kem_mlkem512_MlKem512PrivateKey;

typedef libcrux_ml_kem_types_MlKemPublicKey_be
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
