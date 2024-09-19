module Libcrux_ml_kem.Mlkem512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_C1_BLOCK_SIZE_512_: usize = sz 320

let v_C1_SIZE_512_: usize = sz 640

let v_C2_SIZE_512_: usize = sz 128

let v_CPA_PKE_CIPHERTEXT_SIZE_512_: usize = sz 768

let v_CPA_PKE_PUBLIC_KEY_SIZE_512_: usize = sz 800

let v_CPA_PKE_SECRET_KEY_SIZE_512_: usize = sz 768

let v_ETA1: usize = sz 3

let v_ETA1_RANDOMNESS_SIZE: usize = sz 192

let v_ETA2: usize = sz 2

let v_ETA2_RANDOMNESS_SIZE: usize = sz 128

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = sz 800

let v_RANKED_BYTES_PER_RING_ELEMENT_512_: usize = sz 768

let v_RANK_512_: usize = sz 2

let v_SECRET_KEY_SIZE_512_: usize = sz 1632

let v_T_AS_NTT_ENCODED_SIZE_512_: usize = sz 768

let v_VECTOR_U_COMPRESSION_FACTOR_512_: usize = sz 10

let v_VECTOR_V_COMPRESSION_FACTOR_512_: usize = sz 4

/// Decapsulate ML-KEM 512
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
    : Prims.Pure (t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:t_Array u8 (sz 32) = res in
          let shared_secret, valid =
            Spec.MLKEM.Instances.mlkem512_decapsulate private_key.f_value ciphertext.f_value
          in
          valid ==> res == shared_secret)

/// Encapsulate ML-KEM 512
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768) & t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun res ->
          let res:(Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768) & t_Array u8 (sz 32)) = res in
          let (ciphertext, shared_secret), valid =
            Spec.MLKEM.Instances.mlkem512_encapsulate public_key.f_value randomness
          in
          let res_ciphertext, res_shared_secret = res in
          valid ==> (res_ciphertext.f_value == ciphertext /\ res_shared_secret == shared_secret))

/// Generate ML-KEM 512 Key Pair
/// The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem512KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 1632) (sz 800))
      Prims.l_True
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 1632) (sz 800) = res in
          let (secret_key, public_key), valid =
            Spec.MLKEM.Instances.mlkem512_generate_keypair randomness
          in
          valid ==> (res.f_sk.f_value == secret_key /\ res.f_pk.f_value == public_key))

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800)))
      Prims.l_True
      (fun _ -> Prims.l_True)
