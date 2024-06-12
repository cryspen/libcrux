module Libcrux_ml_kem.Mlkem512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_C1_BLOCK_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_C1_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_C2_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_CIPHERTEXT_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_PUBLIC_KEY_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_SECRET_KEY_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_ETA1: usize = Rust_primitives.Hax.dropped_body

let v_ETA1_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_ETA2: usize = Rust_primitives.Hax.dropped_body

let v_ETA2_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_RANKED_BYTES_PER_RING_ELEMENT_512_: usize = Rust_primitives.Hax.dropped_body

let v_RANK_512_: usize = Rust_primitives.Hax.dropped_body

let v_SECRET_KEY_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_T_AS_NTT_ENCODED_SIZE_512_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_U_COMPRESSION_FACTOR_512_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_V_COMPRESSION_FACTOR_512_: usize = Rust_primitives.Hax.dropped_body

/// An ML-KEM 512 Ciphertext
unfold
let t_MlKem512Ciphertext = Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768)

/// An ML-KEM 512 Private key
unfold
let t_MlKem512PrivateKey = Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 1632)

/// Decapsulate ML-KEM 512
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// An ML-KEM 512 Public key
unfold
let t_MlKem512PublicKey = Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800)

/// Encapsulate ML-KEM 512
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Am ML-KEM 512 Key pair
unfold
let t_MlKem512KeyPair = Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 1632) (sz 800)

/// Generate ML-KEM 512 Key Pair
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem512KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 1632) (sz 800))
      Prims.l_True
      (fun _ -> Prims.l_True)
