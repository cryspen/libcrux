module Libcrux_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

/// The number of bytes
val impl_6__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_13__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_20__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

///An ML-KEM Ciphertext
type t_MlKemCiphertext (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemCiphertext v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE)

/// A reference to the raw byte slice.
val impl_6__as_slice (v_SIZE: usize) (self: t_MlKemCiphertext v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value)

///An ML-KEM Private key
type t_MlKemPrivateKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPrivateKey v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE)

/// A reference to the raw byte slice.
val impl_13__as_slice (v_SIZE: usize) (self: t_MlKemPrivateKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value)

///An ML-KEM Public key
type t_MlKemPublicKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPublicKey v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE)

/// A reference to the raw byte slice.
val impl_20__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value)

/// An ML-KEM key pair
type t_MlKemKeyPair (v_PRIVATE_KEY_SIZE: usize) (v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_MlKemPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_MlKemPublicKey v_PUBLIC_KEY_SIZE
}

/// Create a new [`MlKemKeyPair`] from the secret and public key.
val impl_21__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE = result in
          result.f_sk == sk /\ result.f_pk == pk)

/// Separate this key into the public and private key.
val impl_21__into_parts
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Creates a new [`MlKemKeyPair`].
val impl_21__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get a reference to the raw public key bytes.
val impl_21__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the [`MlKemPrivateKey<PRIVATE_KEY_SIZE>`].
val impl_21__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the [`MlKemPublicKey<PUBLIC_KEY_SIZE>`].
val impl_21__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPublicKey v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the raw private key bytes.
val impl_21__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Unpack an incoming private key into it\'s different parts.
/// We have this here in types to extract into a common core for C.
val unpack_private_key (v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE: usize) (private_key: t_Slice u8)
    : Prims.Pure (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)
      (requires
        Seq.length private_key >=
        v v_CPA_SECRET_KEY_SIZE + v v_PUBLIC_KEY_SIZE + v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE)
      (ensures
        fun result ->
          let result:(t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8) = result in
          let ind_cpa_secret_key_s, rest = split private_key v_CPA_SECRET_KEY_SIZE in
          let ind_cpa_public_key_s, rest = split rest v_PUBLIC_KEY_SIZE in
          let ind_cpa_public_key_hash_s, implicit_rejection_value_s =
            split rest Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
          in
          let
          ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value
          =
            result
          in
          ind_cpa_secret_key_s == ind_cpa_secret_key /\ ind_cpa_public_key_s == ind_cpa_public_key /\
          ind_cpa_public_key_hash_s == ind_cpa_public_key_hash /\
          implicit_rejection_value_s == implicit_rejection_value /\
          Seq.length ind_cpa_secret_key == v v_CPA_SECRET_KEY_SIZE /\
          Seq.length ind_cpa_public_key == v v_PUBLIC_KEY_SIZE /\
          Seq.length ind_cpa_public_key_hash == v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE /\
          Seq.length implicit_rejection_value ==
          Seq.length private_key -
          (v v_CPA_SECRET_KEY_SIZE + v v_PUBLIC_KEY_SIZE +
            v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (v_SIZE: usize) : Core.Default.t_Default (t_MlKemCiphertext v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPrivateKey v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPublicKey v_SIZE)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemCiphertext v_SIZE) (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPrivateKey v_SIZE) (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPublicKey v_SIZE) (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemCiphertext v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from_pre = (fun (value: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun
        (value: t_Slice u8)
        (out: Core.Result.t_Result (t_MlKemCiphertext v_SIZE) Core.Array.t_TryFromSliceError)
        ->
        true);
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match
        Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 v_SIZE)
          #FStar.Tactics.Typeclasses.solve
          value
      with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_MlKemCiphertext v_SIZE)
        <:
        Core.Result.t_Result (t_MlKemCiphertext v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_MlKemCiphertext v_SIZE) Core.Array.t_TryFromSliceError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from_pre = (fun (value: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun
        (value: t_Slice u8)
        (out: Core.Result.t_Result (t_MlKemPrivateKey v_SIZE) Core.Array.t_TryFromSliceError)
        ->
        true);
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match
        Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 v_SIZE)
          #FStar.Tactics.Typeclasses.solve
          value
      with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_MlKemPrivateKey v_SIZE)
        <:
        Core.Result.t_Result (t_MlKemPrivateKey v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_MlKemPrivateKey v_SIZE) Core.Array.t_TryFromSliceError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemPublicKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from_pre = (fun (value: t_Slice u8) -> true);
    f_try_from_post
    =
    (fun
        (value: t_Slice u8)
        (out: Core.Result.t_Result (t_MlKemPublicKey v_SIZE) Core.Array.t_TryFromSliceError)
        ->
        true);
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match
        Core.Convert.f_try_into #(t_Slice u8)
          #(t_Array u8 v_SIZE)
          #FStar.Tactics.Typeclasses.solve
          value
      with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_MlKemPublicKey v_SIZE)
        <:
        Core.Result.t_Result (t_MlKemPublicKey v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_MlKemPublicKey v_SIZE) Core.Array.t_TryFromSliceError
  }
