module Libcrux_ml_kem.Mlkem1024.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1568)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 1024
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 3168))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

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

/// Generate ML-KEM 1024 Key Pair
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 3168) (sz 1568))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encapsulate ML-KEM 1024 (unpacked)
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an unpacked public key of type [`MlKem1024PublicKeyUnpacked`],
/// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
val encapsulate_unpacked
      (public_key:
          Libcrux_ml_kem.Types.Unpacked.t_MlKemPublicKeyUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 1024 (unpacked)
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an unpacked key pair of type [`MlKem1024KeyPairUnpacked`]
/// and an [`MlKem1024Ciphertext`].
val decapsulate_unpacked
      (private_key:
          Libcrux_ml_kem.Types.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1568))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 1024 Key Pair in "unpacked" form
val generate_key_pair_unpacked (randomness: t_Array u8 (sz 64))
    : Prims.Pure
      (Libcrux_ml_kem.Types.Unpacked.t_MlKemKeyPairUnpacked (sz 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)
