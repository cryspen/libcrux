module Libcrux_ml_kem.Mlkem512.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

/// Validate a private key.
/// Returns `true` if valid, and `false` otherwise.
val validate_private_key
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 768))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 512
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (Rust_primitives.mk_usize 1632))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 768))
    : Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 512
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
val encapsulate
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 800))
      (randomness: t_Array u8 (Rust_primitives.mk_usize 32))
    : Prims.Pure
      (Libcrux_ml_kem.Types.t_MlKemCiphertext (Rust_primitives.mk_usize 768) &
        t_Array u8 (Rust_primitives.mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 512 Key Pair
val generate_key_pair (randomness: t_Array u8 (Rust_primitives.mk_usize 64))
    : Prims.Pure
      (Libcrux_ml_kem.Types.t_MlKemKeyPair (Rust_primitives.mk_usize 1632)
          (Rust_primitives.mk_usize 800)) Prims.l_True (fun _ -> Prims.l_True)

/// Validate a public key.
/// Returns `true` if valid, and `false` otherwise.
val validate_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (Rust_primitives.mk_usize 800))
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
