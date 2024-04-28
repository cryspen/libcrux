module Libcrux_ml_kem.Kyber1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ETA1: usize = sz 2

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *! sz 64

let v_ETA2: usize = sz 2

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *! sz 64

let v_RANK_1024_: usize = sz 4

let v_CPA_PKE_SECRET_KEY_SIZE_1024_: usize =
  ((v_RANK_1024_ *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_RANKED_BYTES_PER_RING_ELEMENT_1024_: usize =
  (v_RANK_1024_ *! Libcrux_ml_kem.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! sz 8

let v_T_AS_NTT_ENCODED_SIZE_1024_: usize =
  ((v_RANK_1024_ *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  sz 8

let v_CPA_PKE_PUBLIC_KEY_SIZE_1024_: usize = v_T_AS_NTT_ENCODED_SIZE_1024_ +! sz 32

let v_SECRET_KEY_SIZE_1024_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_1024_ +! v_CPA_PKE_PUBLIC_KEY_SIZE_1024_ <: usize) +!
    Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

let v_VECTOR_U_COMPRESSION_FACTOR_1024_: usize = sz 11

let v_C1_BLOCK_SIZE_1024_: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR_1024_
    <:
    usize) /!
  sz 8

let v_C1_SIZE_1024_: usize = v_C1_BLOCK_SIZE_1024_ *! v_RANK_1024_

let v_VECTOR_V_COMPRESSION_FACTOR_1024_: usize = sz 5

let v_C2_SIZE_1024_: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR_1024_
    <:
    usize) /!
  sz 8

let v_CPA_PKE_CIPHERTEXT_SIZE_1024_: usize = v_C1_SIZE_1024_ +! v_C2_SIZE_1024_

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE_1024_

unfold
let t_MlKem1024Ciphertext = Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568)

unfold
let t_MlKem1024PrivateKey = Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168)

unfold
let t_MlKem1024PublicKey = Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)

/// Decapsulate ML-KEM 1024
val decapsulate
      (secret_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 1024
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate ML-KEM 1024 Key Pair
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 3168) (sz 1568))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)))
      Prims.l_True
      (fun _ -> Prims.l_True)
