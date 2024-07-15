module Libcrux_ml_kem.Mlkem768.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Validate a public key.
/// Returns `Some(public_key)` if valid, and `None` otherwise.
val validate_public_key (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184))
    : Prims.Pure (Core.Option.t_Option (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 1184)))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 768
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
val decapsulate
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (sz 2400))
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

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

/// Generate ML-KEM 768 Key Pair
val generate_key_pair (randomness: t_Array u8 (sz 64))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemKeyPair (sz 2400) (sz 1184))
      Prims.l_True
      (fun _ -> Prims.l_True)

let _ =
    (* This module has implicit dependencies, here we make them explicit. *)
    (* The implicit dependencies arise from typeclasses instances. *)
    let open Libcrux_ml_kem.Vector.Portable in
    let open Libcrux_ml_kem.Vector.Neon in
    ()

/// Encapsulate ML-KEM 768 (unpacked)
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an unpacked public key of type [`MlKem768PublicKeyUnpacked`],
/// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
val encapsulate_unpacked
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 768 (unpacked)
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an unpacked key pair of type [`MlKem768KeyPairUnpacked`]
/// and an [`MlKem768Ciphertext`].
val decapsulate_unpacked
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 1088))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 768 Key Pair in "unpacked" form
val generate_key_pair_unpacked (randomness: t_Array u8 (sz 64))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 3)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)
