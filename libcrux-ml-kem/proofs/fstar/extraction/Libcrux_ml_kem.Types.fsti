module Libcrux_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The number of bytes
val impl_7__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_14__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// The number of bytes
val impl_21__len: v_SIZE: usize -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

///An ML-KEM Ciphertext
type t_MlKemCiphertext (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemCiphertext v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemCiphertext v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MlKemCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemCiphertext v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemCiphertext v_SIZE) -> true);
    f_as_ref_post = (fun (self: t_MlKemCiphertext v_SIZE) (out: t_Slice u8) -> true);
    f_as_ref = fun (self: t_MlKemCiphertext v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemCiphertext v_SIZE) -> true);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemCiphertext v_SIZE) (t_Array u8 v_SIZE) =
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
let impl_5 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemCiphertext v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemCiphertext v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemCiphertext v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemCiphertext v_SIZE) -> value.f_value
  }

/// A reference to the raw byte slice.
val impl_7__as_slice (v_SIZE: usize) (self: t_MlKemCiphertext v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

///An ML-KEM Private key
type t_MlKemPrivateKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPrivateKey v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemPrivateKey v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MlKemPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemPrivateKey v_SIZE) -> true);
    f_as_ref_post = (fun (self: t_MlKemPrivateKey v_SIZE) (out: t_Slice u8) -> true);
    f_as_ref = fun (self: t_MlKemPrivateKey v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemPrivateKey v_SIZE) -> true);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
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
let impl_12 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPrivateKey v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemPrivateKey v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemPrivateKey v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemPrivateKey v_SIZE) -> value.f_value
  }

/// A reference to the raw byte slice.
val impl_14__as_slice (v_SIZE: usize) (self: t_MlKemPrivateKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

///An ML-KEM Public key
type t_MlKemPublicKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15 (v_SIZE: usize) : Core.Default.t_Default (t_MlKemPublicKey v_SIZE) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_MlKemPublicKey v_SIZE) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = Rust_primitives.Hax.repeat 0uy v_SIZE } <: t_MlKemPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16 (v_SIZE: usize) : Core.Convert.t_AsRef (t_MlKemPublicKey v_SIZE) (t_Slice u8) =
  {
    f_as_ref_pre = (fun (self: t_MlKemPublicKey v_SIZE) -> true);
    f_as_ref_post = (fun (self: t_MlKemPublicKey v_SIZE) (out: t_Slice u8) -> true);
    f_as_ref = fun (self: t_MlKemPublicKey v_SIZE) -> self.f_value <: t_Slice u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from_pre = (fun (value: t_Array u8 v_SIZE) -> true);
    f_from_post = (fun (value: t_Array u8 v_SIZE) (out: t_MlKemPublicKey v_SIZE) -> true);
    f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_MlKemPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18 (v_SIZE: usize) : Core.Convert.t_From (t_MlKemPublicKey v_SIZE) (t_Array u8 v_SIZE) =
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
let impl_19 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_MlKemPublicKey v_SIZE) =
  {
    f_from_pre = (fun (value: t_MlKemPublicKey v_SIZE) -> true);
    f_from_post = (fun (value: t_MlKemPublicKey v_SIZE) (out: t_Array u8 v_SIZE) -> true);
    f_from = fun (value: t_MlKemPublicKey v_SIZE) -> value.f_value
  }

/// A reference to the raw byte slice.
val impl_21__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE)
    : Prims.Pure (t_Array u8 v_SIZE) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemCiphertext v_SIZE) (t_Slice u8) =
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
let impl_13 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemPrivateKey v_SIZE) (t_Slice u8) =
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
let impl_20 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_MlKemPublicKey v_SIZE) (t_Slice u8) =
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

/// An ML-KEM key pair
type t_MlKemKeyPair (v_PRIVATE_KEY_SIZE: usize) (v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_MlKemPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_MlKemPublicKey v_PUBLIC_KEY_SIZE
}

/// Create a new [`MlKemKeyPair`] from the secret and public key.
val impl__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Separate this key into the public and private key.
val impl__into_parts
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Creates a new [`MlKemKeyPair`].
val impl__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Get a reference to the raw public key bytes.
val impl__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the [`MlKemPrivateKey<PRIVATE_KEY_SIZE>`].
val impl__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the [`MlKemPublicKey<PUBLIC_KEY_SIZE>`].
val impl__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_MlKemPublicKey v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Get a reference to the raw private key bytes.
val impl__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)
