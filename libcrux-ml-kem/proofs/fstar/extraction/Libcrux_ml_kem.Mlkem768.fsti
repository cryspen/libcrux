module Libcrux_ml_kem.Mlkem768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_C1_BLOCK_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_C1_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_C2_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_CIPHERTEXT_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_PUBLIC_KEY_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_CPA_PKE_SECRET_KEY_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_ETA1: usize = Rust_primitives.Hax.dropped_body

let v_ETA1_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_ETA2: usize = Rust_primitives.Hax.dropped_body

let v_ETA2_RANDOMNESS_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = Rust_primitives.Hax.dropped_body

let v_RANKED_BYTES_PER_RING_ELEMENT_768_: usize = Rust_primitives.Hax.dropped_body

let v_RANK_768_: usize = Rust_primitives.Hax.dropped_body

let v_SECRET_KEY_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_T_AS_NTT_ENCODED_SIZE_768_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_U_COMPRESSION_FACTOR_768_: usize = Rust_primitives.Hax.dropped_body

let v_VECTOR_V_COMPRESSION_FACTOR_768_: usize = Rust_primitives.Hax.dropped_body

/// An ML-KEM 768 Ciphertext
unfold
let t_MlKem768Ciphertext = Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088)

/// An ML-KEM 768 Private key
unfold
let t_MlKem768PrivateKey = Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400)

/// Decapsulate ML-KEM 768
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// An ML-KEM 768 Public key
unfold
let t_MlKem768PublicKey = Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184)

/// Encapsulate ML-KEM 768
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Am ML-KEM 768 Key pair
unfold
let t_MlKem768KeyPair = Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 2400) (sz 1184)

/// Generate ML-KEM 768 Key Pair
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
/// This function uses CPU feature detection to pick the most efficient version
/// on each platform. To use a specific version with your own feature detection
/// use one of the following
/// - [`generate_key_pair_avx2`]
/// - [`generate_key_pair_neon`]
/// - [`generate_key_pair_portable`]
/// This function returns an [`MlKem768KeyPair`].
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 2400) (sz 1184))
      Prims.l_True
      (fun _ -> Prims.l_True)
