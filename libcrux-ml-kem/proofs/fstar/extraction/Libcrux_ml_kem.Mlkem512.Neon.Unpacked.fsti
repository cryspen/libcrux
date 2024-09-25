module Libcrux_ml_kem.Mlkem512.Neon.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Neon in
  ()

let _ =
        (* This module has implicit dependencies, here we make them explicit. *)
        (* The implicit dependencies arise from typeclasses instances. *)
        let open Libcrux_ml_kem.Vector.Portable in
        let open Libcrux_ml_kem.Vector.Neon in
        ()

/// Encapsulate ML-KEM 512 (unpacked)
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an unpacked public key of type [`MlKem512PublicKeyUnpacked`],
/// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
val encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768) & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Create a new, empty unpacked public key.
val init_public_key: Prims.unit
  -> Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the unpacked public key.
val unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (sz 800))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (sz 2)
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 512 (unpacked)
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an unpacked key pair of type [`MlKem512KeyPairUnpacked`]
/// and an [`MlKem512Ciphertext`].
val decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (sz 768))
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate ML-KEM 512 Key Pair in "unpacked" form
val generate_key_pair
      (randomness: t_Array u8 (sz 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 2)
            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 2)
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Create a new, empty unpacked key.
val init_key_pair: Prims.unit
  -> Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (sz 2)
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
