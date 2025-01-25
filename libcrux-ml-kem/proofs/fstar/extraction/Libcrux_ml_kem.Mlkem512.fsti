module Libcrux_ml_kem.Mlkem512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let v_RANK_512_: usize = mk_usize 2

let v_RANKED_BYTES_PER_RING_ELEMENT_512_: usize =
  (v_RANK_512_ *! Libcrux_ml_kem.Constants.v_BITS_PER_RING_ELEMENT <: usize) /! mk_usize 8

let v_T_AS_NTT_ENCODED_SIZE_512_: usize =
  ((v_RANK_512_ *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_VECTOR_U_COMPRESSION_FACTOR_512_: usize = mk_usize 10

let v_C1_BLOCK_SIZE_512_: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_U_COMPRESSION_FACTOR_512_
    <:
    usize) /!
  mk_usize 8

let v_C1_SIZE_512_: usize = v_C1_BLOCK_SIZE_512_ *! v_RANK_512_

let v_VECTOR_V_COMPRESSION_FACTOR_512_: usize = mk_usize 4

let v_C2_SIZE_512_: usize =
  (Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_VECTOR_V_COMPRESSION_FACTOR_512_
    <:
    usize) /!
  mk_usize 8

let v_CPA_PKE_SECRET_KEY_SIZE_512_: usize =
  ((v_RANK_512_ *! Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *!
    Libcrux_ml_kem.Constants.v_BITS_PER_COEFFICIENT
    <:
    usize) /!
  mk_usize 8

let v_CPA_PKE_PUBLIC_KEY_SIZE_512_: usize = v_T_AS_NTT_ENCODED_SIZE_512_ +! mk_usize 32

let v_CPA_PKE_CIPHERTEXT_SIZE_512_: usize = v_C1_SIZE_512_ +! v_C2_SIZE_512_

let v_SECRET_KEY_SIZE_512_: usize =
  ((v_CPA_PKE_SECRET_KEY_SIZE_512_ +! v_CPA_PKE_PUBLIC_KEY_SIZE_512_ <: usize) +!
    Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
    <:
    usize) +!
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE

let v_ETA1: usize = mk_usize 3

let v_ETA1_RANDOMNESS_SIZE: usize = v_ETA1 *! mk_usize 64

let v_ETA2: usize = mk_usize 2

let v_ETA2_RANDOMNESS_SIZE: usize = v_ETA2 *! mk_usize 64

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
  Libcrux_ml_kem.Constants.v_SHARED_SECRET_SIZE +! v_CPA_PKE_CIPHERTEXT_SIZE_512_

/// Validate a public key.
/// Returns `true` if valid, and `false` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Validate a private key.
/// Returns `true` if valid, and `false` otherwise.
val validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 512 Key Pair
/// The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem512KeyPair`].
val generate_key_pair (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 1632) (mk_usize 800))
      Prims.l_True
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Types.t_MlKemKeyPair (mk_usize 1632) (mk_usize 800) = res in
          let (secret_key, public_key), valid =
            Spec.MLKEM.Instances.mlkem512_generate_keypair randomness
          in
          valid ==> (res.f_sk.f_value == secret_key /\ res.f_pk.f_value == public_key))

/// Encapsulate ML-KEM 512
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 800))
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768) & t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:(Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768) & t_Array u8 (mk_usize 32))
          =
            res
          in
          let (ciphertext, shared_secret), valid =
            Spec.MLKEM.Instances.mlkem512_encapsulate public_key.f_value randomness
          in
          let res_ciphertext, res_shared_secret = res in
          valid ==> (res_ciphertext.f_value == ciphertext /\ res_shared_secret == shared_secret))

/// Decapsulate ML-KEM 512
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 768))
    : Prims.Pure (t_Array u8 (mk_usize 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:t_Array u8 (mk_usize 32) = res in
          let shared_secret, valid =
            Spec.MLKEM.Instances.mlkem512_decapsulate private_key.f_value ciphertext.f_value
          in
          valid ==> res == shared_secret)
