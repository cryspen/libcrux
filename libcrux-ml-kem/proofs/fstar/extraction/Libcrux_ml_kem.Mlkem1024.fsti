module Libcrux_ml_kem.Mlkem1024
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_C1_BLOCK_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_C1_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_C2_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_CIPHERTEXT_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_PUBLIC_KEY_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_SECRET_KEY_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_ETA1: usize = Rust_primitives.Hax.dropped_body

let v_ETA1_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_ETA2: usize = Rust_primitives.Hax.dropped_body

let v_ETA2_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_RANKED_BYTES_PER_RING_ELEMENT_1024_: usize = Rust_primitives.Hax.dropped_body

let v_RANK_1024_: usize = Rust_primitives.Hax.dropped_body

let v_SECRET_KEY_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_T_AS_NTT_ENCODED_SIZE_1024_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_U_COMPRESSION_FACTOR_1024_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_V_COMPRESSION_FACTOR_1024_: usize = Rust_primitives.Hax.dropped_body

/// An ML-KEM 1024 Ciphertext
unfold
let t_MlKem1024Ciphertext = Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568)

/// An ML-KEM 1024 Private key
unfold
let t_MlKem1024PrivateKey = Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168)

/// Decapsulate ML-KEM 1024
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// An ML-KEM 1024 Public key
unfold
let t_MlKem1024PublicKey = Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)

/// Encapsulate ML-KEM 1024
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Am ML-KEM 1024 Key pair
unfold
let t_MlKem1024KeyPair = Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 3168) (sz 1568)

/// Generate ML-KEM 1024 Key Pair
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function returns an [`MlKem1024KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 3168) (sz 1568))
      Prims.l_True
      (fun _ -> Prims.l_True)
