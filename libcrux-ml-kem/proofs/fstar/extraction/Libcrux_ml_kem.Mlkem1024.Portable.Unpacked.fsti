module Libcrux_ml_kem.Mlkem1024.Portable.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Unpacked in
  let open Libcrux_ml_kem.Vector.Portable in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Create a new, empty unpacked key.
val init_key_pair: Prims.unit
  -> Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Create a new, empty unpacked public key.
val init_public_key: Prims.unit
  -> Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val serialized_public_key
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (requires
        forall (i: nat).
          i < 4 ==>
          Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index public_key
                  .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
                  .Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
                i))
      (fun _ -> Prims.l_True)

/// Get the serialized private key.
val key_pair_serialized_private_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized private key.
val key_pair_serialized_private_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val key_pair_serialized_public_key_mut
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (requires
        forall (i: nat).
          i < 4 ==>
          Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index key_pair
                  .Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key
                  .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
                  .Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
                i))
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val key_pair_serialized_public_key
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (requires
        forall (i: nat).
          i < 4 ==>
          Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index key_pair
                  .Libcrux_ml_kem.Ind_cca.Unpacked.f_public_key
                  .Libcrux_ml_kem.Ind_cca.Unpacked.f_ind_cpa_public_key
                  .Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
                i))
      (fun _ -> Prims.l_True)

/// Get an unpacked key from a private key.
val key_pair_from_private_mut
      (private_key: Libcrux_ml_kem.Types.t_MlKemPrivateKey (mk_usize 3168))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the unpacked public key.
val unpacked_public_key
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey (mk_usize 1568))
      (unpacked_public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate ML-KEM 1024 Key Pair in "unpacked" form
val generate_key_pair_mut
      (randomness: t_Array u8 (mk_usize 64))
      (key_pair:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate ML-KEM 1024 Key Pair in "unpacked" form.
val generate_key_pair (randomness: t_Array u8 (mk_usize 64))
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      Prims.l_True
      (fun _ -> Prims.l_True)

let _ =
        (* This module has implicit dependencies, here we make them explicit. *)
        (* The implicit dependencies arise from typeclasses instances. *)
        let open Libcrux_ml_kem.Vector.Portable in
        let open Libcrux_ml_kem.Vector.Neon in
        ()

/// Encapsulate ML-KEM 1024 (unpacked)
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an unpacked public key of type [`MlKem1024PublicKeyUnpacked`],
/// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
/// TODO: The F* prefix opens required modules, it should go away when the following issue is resolved:
/// <https://github.com/hacspec/hax/issues/770>
val encapsulate
      (public_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemPublicKeyUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (randomness: t_Array u8 (mk_usize 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568) & t_Array u8 (mk_usize 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decapsulate ML-KEM 1024 (unpacked)
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an unpacked key pair of type [`MlKem1024KeyPairUnpacked`]
/// and an [`MlKem1024Ciphertext`].
val decapsulate
      (private_key:
          Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked (mk_usize 4)
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext (mk_usize 1568))
    : Prims.Pure (t_Array u8 (mk_usize 32)) Prims.l_True (fun _ -> Prims.l_True)
