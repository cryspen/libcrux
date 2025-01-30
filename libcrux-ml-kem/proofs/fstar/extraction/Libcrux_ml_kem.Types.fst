module Libcrux_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

///An ML-KEM Ciphertext
type t_MlKemCiphertext (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_SIZE: usize) : Core.Default.t_Default (t_MlKemCiphertext v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemCiphertext v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MlKemCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemCiphertext v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemCiphertext v_SIZE) -> true);
    f_as_ref_post
    =
    (fun (self_: t_MlKemCiphertext v_SIZE) (result: t_Slice u8) -> result = self_.f_value);
    f_as_ref = fun (self: t_MlKemCiphertext v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemCiphertext v_SIZE) -> result.f_value = value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemCiphertext v_SIZE) -> true);
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone #(t_Array u8 v_SIZE) #FStar.Tactics.Typeclasses.solve value }
      <:
      t_MlKemCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemCiphertext v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemCiphertext v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemCiphertext v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemCiphertext v_SIZE) -> value.f_value
  }

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
        <:
        Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError
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

/// The number of bytes
let impl_6__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// A reference to the raw byte slice.
let impl_6__as_slice (v_SIZE: usize) (self: t_MlKemCiphertext v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value) = self.f_value

///An ML-KEM Private key
type t_MlKemPrivateKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPrivateKey v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemPrivateKey v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MlKemPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemPrivateKey v_SIZE) -> true);
    f_as_ref_post
    =
    (fun (self_: t_MlKemPrivateKey v_SIZE) (result: t_Slice u8) -> result = self_.f_value);
    f_as_ref = fun (self: t_MlKemPrivateKey v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemPrivateKey v_SIZE) -> result.f_value = value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemPrivateKey v_SIZE) -> true);
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone #(t_Array u8 v_SIZE) #FStar.Tactics.Typeclasses.solve value }
      <:
      t_MlKemPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPrivateKey v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemPrivateKey v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemPrivateKey v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemPrivateKey v_SIZE) -> value.f_value
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
        <:
        Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError
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

/// The number of bytes
let impl_13__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// A reference to the raw byte slice.
let impl_13__as_slice (v_SIZE: usize) (self: t_MlKemPrivateKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value) = self.f_value

///An ML-KEM Public key
type t_MlKemPublicKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPublicKey v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemPublicKey v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat (mk_u8 0) v_SIZE } <: t_MlKemPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPublicKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemPublicKey v_SIZE) -> true);
    f_as_ref_post
    =
    (fun (self_: t_MlKemPublicKey v_SIZE) (result: t_Slice u8) -> result = self_.f_value);
    f_as_ref = fun (self: t_MlKemPublicKey v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post
    =
    (fun (value: t_Array u8 v_SIZE) (result: t_MlKemPublicKey v_SIZE) -> result.f_value = value);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemPublicKey v_SIZE) -> true);
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone #(t_Array u8 v_SIZE) #FStar.Tactics.Typeclasses.solve value }
      <:
      t_MlKemPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPublicKey v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemPublicKey v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemPublicKey v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemPublicKey v_SIZE) -> value.f_value
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
        <:
        Core.Result.t_Result (t_Array u8 v_SIZE) Core.Array.t_TryFromSliceError
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

/// The number of bytes
let impl_20__len (v_SIZE: usize) (_: Prims.unit) : usize = v_SIZE

/// A reference to the raw byte slice.
let impl_20__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 v_SIZE = result in
          result == self.f_value) = self.f_value

/// An ML-KEM key pair
type t_MlKemKeyPair (v_PRIVATE_KEY_SIZE: usize) (v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_MlKemPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_MlKemPublicKey v_PUBLIC_KEY_SIZE
}

/// Creates a new [`MlKemKeyPair`].
let impl_21__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  {
    f_sk
    =
    Core.Convert.f_into #(t_Array u8 v_PRIVATE_KEY_SIZE)
      #(t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      sk;
    f_pk
    =
    Core.Convert.f_into #(t_Array u8 v_PUBLIC_KEY_SIZE)
      #(t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      #FStar.Tactics.Typeclasses.solve
      pk
  }
  <:
  t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

/// Get a reference to the [`MlKemPublicKey<PUBLIC_KEY_SIZE>`].
let impl_21__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_MlKemPublicKey v_PUBLIC_KEY_SIZE = self.f_pk

/// Get a reference to the [`MlKemPrivateKey<PRIVATE_KEY_SIZE>`].
let impl_21__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_MlKemPrivateKey v_PRIVATE_KEY_SIZE = self.f_sk

/// Get a reference to the raw public key bytes.
let impl_21__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PUBLIC_KEY_SIZE = impl_20__as_slice v_PUBLIC_KEY_SIZE self.f_pk

/// Get a reference to the raw private key bytes.
let impl_21__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PRIVATE_KEY_SIZE = impl_13__as_slice v_PRIVATE_KEY_SIZE self.f_sk

/// Separate this key into the public and private key.
let impl_21__into_parts
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE) =
  self.f_sk, self.f_pk
  <:
  (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE)

/// Create a new [`MlKemKeyPair`] from the secret and public key.
let impl_21__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (ensures
        fun result ->
          let result:t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE = result in
          result.f_sk == sk /\ result.f_pk == pk) =
  { f_sk = sk; f_pk = pk } <: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

/// Unpack an incoming private key into it\'s different parts.
/// We have this here in types to extract into a common core for C.
let unpack_private_key (v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE: usize) (private_key: t_Slice u8)
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
            v Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE)) =
  let ind_cpa_secret_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 private_key v_CPA_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key v_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 secret_key Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE
  in
  ind_cpa_secret_key, ind_cpa_public_key, ind_cpa_public_key_hash, implicit_rejection_value
  <:
  (t_Slice u8 & t_Slice u8 & t_Slice u8 & t_Slice u8)
