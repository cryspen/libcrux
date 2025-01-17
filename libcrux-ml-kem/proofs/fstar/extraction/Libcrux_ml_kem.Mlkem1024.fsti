module Libcrux_ml_kem.Mlkem1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_RANK: usize = mk_usize 4

let v_RANKED_BYTES_PER_RING_ELEMENT: usize =
  (v_RANK *! Libcrux_ml_kem.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! mk_usize 8

let v_T_AS_NTT_ENCODED_SIZE: usize =
  ((v_RANK *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_VECTOR_U_COMPRESSION_FACTOR: usize = mk_usize 11

let v_C1_BLOCK_SIZE: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR <: usize
  ) /!
  mk_usize 8

let v_C1_SIZE: usize = v_C1_BLOCK_SIZE *! v_RANK

let v_VECTOR_V_COMPRESSION_FACTOR: usize = mk_usize 5

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
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Validate a private key.
/// Returns `true` if valid, and `false` otherwise.
val validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 1024 Key Pair
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem1024KeyPair`].
val generate_key_pair (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 3168) (mk_usize 1568))
      Prims.l_True
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 3168) (mk_usize 1568) = res in
          let (secret_key, public_key), valid =
            Spec.MLKEM.Instances.mlkem1024_generate_keypair randomness
          in
          valid ==> (res.f_sk.f_value == secret_key /\ res.f_pk.f_value == public_key))

/// Encapsulate ML-KEM 1024
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568) & t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:(Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568) & t_Array u8 (mk_usize 32)
          ) =
            res
          in
          let (ciphertext, shared_secret), valid =
            Spec.MLKEM.Instances.mlkem1024_encapsulate public_key.f_value randomness
          in
          let res_ciphertext, res_shared_secret = res in
          valid ==> (res_ciphertext.f_value == ciphertext /\ res_shared_secret == shared_secret))

/// Decapsulate ML-KEM 1024
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568))
    : Prims.Pure (t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:t_Array u8 (mk_usize 32) = res in
          let shared_secret, valid =
            Spec.MLKEM.Instances.mlkem1024_decapsulate private_key.f_value ciphertext.f_value
          in
          valid ==> res == shared_secret)
