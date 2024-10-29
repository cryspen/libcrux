module Libcrux_ml_kem.Ind_cca.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_ml_kem.Polynomial in
  let open Libcrux_ml_kem.Types in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector;
  f_implicit_rejection_value:t_Array u8 (sz 32)
}

/// An unpacked ML-KEM IND-CCA Private Key
type t_MlKemPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_ind_cpa_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector;
  f_public_key_hash:t_Array u8 (sz 32)
}

/// Get the serialized public key.
val impl__serialized_public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val impl__serialized_public_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Default.t_Default (t_MlKemPublicKeyUnpacked v_K v_Vector) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemPublicKeyUnpacked v_K v_Vector) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      {
        f_ind_cpa_public_key
        =
        Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K
              v_Vector)
          #FStar.Tactics.Typeclasses.solve
          ();
        f_public_key_hash = Rust_primitives.Hax.repeat 0uy (sz 32)
      }
      <:
      t_MlKemPublicKeyUnpacked v_K v_Vector
  }

val encapsulate
      (v_K v_CIPHERTEXT_SIZE v_PUBLIC_KEY_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
      (randomness: t_Array u8 (sz 32))
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE & t_Array u8 (sz 32))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Generate an unpacked key from a serialized key.
val unpack_public_key
      (v_K v_T_AS_NTT_ENCODED_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Hasher #v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (public_key: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      (unpacked_public_key: t_MlKemPublicKeyUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPublicKeyUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// An unpacked ML-KEM KeyPair
type t_MlKemKeyPairUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_private_key:t_MlKemPrivateKeyUnpacked v_K v_Vector;
  f_public_key:t_MlKemPublicKeyUnpacked v_K v_Vector
}

/// Get the serialized public key.
val impl_2__private_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPrivateKeyUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Get the serialized public key.
val impl_2__public_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemPublicKeyUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

/// Get the serialized private key.
val impl_2__serialized_private_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPrivateKey v_K) Prims.l_True (fun _ -> Prims.l_True)

/// Get the serialized public key.
val impl_2__serialized_public_key
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get the serialized public key.
val impl_2__serialized_public_key_mut
      (v_K: usize)
      (#v_Vector: Type0)
      (v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (self: t_MlKemKeyPairUnpacked v_K v_Vector)
      (serialized: Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (Libcrux_ml_kem.Types.t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Default.t_Default (t_MlKemKeyPairUnpacked v_K v_Vector) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemKeyPairUnpacked v_K v_Vector) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      {
        f_private_key
        =
        {
          f_ind_cpa_private_key
          =
          Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K
                v_Vector)
            #FStar.Tactics.Typeclasses.solve
            ();
          f_implicit_rejection_value = Rust_primitives.Hax.repeat 0uy (sz 32)
        }
        <:
        t_MlKemPrivateKeyUnpacked v_K v_Vector;
        f_public_key
        =
        Core.Default.f_default #(t_MlKemPublicKeyUnpacked v_K v_Vector)
          #FStar.Tactics.Typeclasses.solve
          ()
      }
      <:
      t_MlKemKeyPairUnpacked v_K v_Vector
  }

/// Create a new empty unpacked key pair.
val impl_2__new:
    v_K: usize ->
    #v_Vector: Type0 ->
    {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |} ->
    Prims.unit
  -> Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_pair: t_MlKemKeyPairUnpacked v_K v_Vector)
      (ciphertext: Libcrux_ml_kem.Types.t_MlKemCiphertext v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Generate Unpacked Keys
val generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (randomness: t_Array u8 (sz 64))
      (out: t_MlKemKeyPairUnpacked v_K v_Vector)
    : Prims.Pure (t_MlKemKeyPairUnpacked v_K v_Vector) Prims.l_True (fun _ -> Prims.l_True)
