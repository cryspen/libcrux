module Libcrux_ml_kem.Mlkem768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_RANK: usize = mk_usize 3

let v_T_AS_NTT_ENCODED_SIZE: usize =
  ((v_RANK *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_VECTOR_U_COMPRESSION_FACTOR: usize = mk_usize 10

let v_C1_BLOCK_SIZE: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR <: usize
  ) /!
  mk_usize 8

let v_C1_SIZE: usize = v_C1_BLOCK_SIZE *! v_RANK

let v_VECTOR_V_COMPRESSION_FACTOR: usize = mk_usize 4

let v_C2_SIZE: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR <: usize
  ) /!
  mk_usize 8

let v_CPA_PKE_SECRET_KEY_SIZE: usize =
  ((v_RANK *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_CPA_PKE_PUBLIC_KEY_SIZE: usize = v_T_AS_NTT_ENCODED_SIZE +! mk_usize 32

let v_CPA_PKE_CIPHERTEXT_SIZE: usize = v_C1_SIZE +! v_C2_SIZE

let v_SECRET_KEY_SIZE: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE +! v_CPA_PKE_PUBLIC_KEY_SIZE <: usize) +!
    Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

let v_ETA1: usize = mk_usize 2

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *! mk_usize 64

let v_ETA2: usize = mk_usize 2

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *! mk_usize 64

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE

/// Validate a public key.
/// Returns `true` if valid, and `false` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Validate a private key.
/// Returns `true` if valid, and `false` otherwise.
val validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 768 Key Pair
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem768KeyPair`].
val generate_key_pair (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 2400) (mk_usize 1184))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 768
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1184))
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088) & t_Array u8 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 768
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1088))
    : Prims.Pure (t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:t_Array u8 (mk_usize 32) = res in
          let shared_secret, valid =
            Spec.MLKEM.Instances.mlkem768_decapsulate private_key.f_value ciphertext.f_value
          in
          valid ==> res == shared_secret)
