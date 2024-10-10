module Libcrux_ml_kem.Mlkem768.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Validate a private key.
/// Returns `true` if valid, and `false` otherwise.
val validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 1088))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 768
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 1088))
    : Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 768
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 1184))
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 1088) &
        t_Array u8 (Rust_primitives.mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 768 Key Pair
val generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 64))
    : Prims.Pure
      (Libcrux_ml_kem.Types.t_MlKemKeyPair (Rust_primitives.mk_usize 2400)
          (Rust_primitives.mk_usize 1184)) Prims.l_True (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `true` if valid, and `false` otherwise.
val validate_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 1184))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
