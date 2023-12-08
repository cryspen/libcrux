module Libcrux.Kem.Kyber.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_KyberCiphertext (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  { f_as_ref = fun (self: t_KyberCiphertext v_SIZE) -> Rust_primitives.unsize self.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_KyberCiphertext v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (v_SIZE: usize) : Core.Convert.t_From (t_KyberCiphertext v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone value } <: t_KyberCiphertext v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberCiphertext v_SIZE) =
  { f_from = fun (value: t_KyberCiphertext v_SIZE) -> value.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberCiphertext v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match Core.Convert.f_try_into value with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_KyberCiphertext v_SIZE)
        <:
        Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_KyberCiphertext v_SIZE) Core.Array.t_TryFromSliceError
  }

let impl_6__as_slice (v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_6__len (v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) : usize = v_SIZE

let impl_6__split_at (v_SIZE: usize) (self: t_KyberCiphertext v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

type t_KyberPrivateKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
  { f_as_ref = fun (self: t_KyberPrivateKey v_SIZE) -> Rust_primitives.unsize self.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_KyberPrivateKey v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (v_SIZE: usize) : Core.Convert.t_From (t_KyberPrivateKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone value } <: t_KyberPrivateKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPrivateKey v_SIZE) =
  { f_from = fun (value: t_KyberPrivateKey v_SIZE) -> value.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPrivateKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match Core.Convert.f_try_into value with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_KyberPrivateKey v_SIZE)
        <:
        Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_KyberPrivateKey v_SIZE) Core.Array.t_TryFromSliceError
  }

let impl_12__as_slice (v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_12__len (v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) : usize = v_SIZE

let impl_12__split_at (v_SIZE: usize) (self: t_KyberPrivateKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

type t_KyberPublicKey (v_SIZE: usize) = { f_value:t_Array u8 v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13 (v_SIZE: usize) : Core.Convert.t_AsRef (t_KyberPublicKey v_SIZE) (t_Slice u8) =
  { f_as_ref = fun (self: t_KyberPublicKey v_SIZE) -> Rust_primitives.unsize self.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14 (v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  { f_from = fun (value: t_Array u8 v_SIZE) -> { f_value = value } <: t_KyberPublicKey v_SIZE }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15 (v_SIZE: usize) : Core.Convert.t_From (t_KyberPublicKey v_SIZE) (t_Array u8 v_SIZE) =
  {
    f_from
    =
    fun (value: t_Array u8 v_SIZE) ->
      { f_value = Core.Clone.f_clone value } <: t_KyberPublicKey v_SIZE
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16 (v_SIZE: usize) : Core.Convert.t_From (t_Array u8 v_SIZE) (t_KyberPublicKey v_SIZE) =
  { f_from = fun (value: t_KyberPublicKey v_SIZE) -> value.f_value }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17 (v_SIZE: usize) : Core.Convert.t_TryFrom (t_KyberPublicKey v_SIZE) (t_Slice u8) =
  {
    f_Error = Core.Array.t_TryFromSliceError;
    f_try_from
    =
    fun (value: t_Slice u8) ->
      match Core.Convert.f_try_into value with
      | Core.Result.Result_Ok value ->
        Core.Result.Result_Ok ({ f_value = value } <: t_KyberPublicKey v_SIZE)
        <:
        Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError
      | Core.Result.Result_Err e ->
        Core.Result.Result_Err e
        <:
        Core.Result.t_Result (t_KyberPublicKey v_SIZE) Core.Array.t_TryFromSliceError
  }

let impl_18__as_slice (v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : t_Array u8 v_SIZE =
  self.f_value

let impl_18__len (v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) : usize = v_SIZE

let impl_18__split_at (v_SIZE: usize) (self: t_KyberPublicKey v_SIZE) (mid: usize)
    : (t_Slice u8 & t_Slice u8) =
  Core.Slice.impl__split_at (Rust_primitives.unsize self.f_value <: t_Slice u8) mid

type t_KyberKeyPair (v_PRIVATE_KEY_SIZE: usize) (v_PUBLIC_KEY_SIZE: usize) = {
  f_sk:t_KyberPrivateKey v_PRIVATE_KEY_SIZE;
  f_pk:t_KyberPublicKey v_PUBLIC_KEY_SIZE
}

let impl__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_KyberPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_KyberPublicKey v_PUBLIC_KEY_SIZE)
    : t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { f_sk = sk; f_pk = pk } <: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

let impl__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
    : t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE =
  { f_sk = Core.Convert.f_into sk; f_pk = Core.Convert.f_into pk }
  <:
  t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

let impl__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PUBLIC_KEY_SIZE = impl_18__as_slice v_PUBLIC_KEY_SIZE self.f_pk

let impl__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_KyberPrivateKey v_PRIVATE_KEY_SIZE = self.f_sk

let impl__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_KyberPublicKey v_PUBLIC_KEY_SIZE = self.f_pk

let impl__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_KyberKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
    : t_Array u8 v_PRIVATE_KEY_SIZE = impl_12__as_slice v_PRIVATE_KEY_SIZE self.f_sk
