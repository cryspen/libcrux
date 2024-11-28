module Libcrux_ml_kem.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let impl_7__as_slice (v_SIZE: usize) (self: t_MlKemCiphertext v_SIZE) = self.f_value

let impl_7__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

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

let impl_14__as_slice (v_SIZE: usize) (self: t_MlKemPrivateKey v_SIZE) = self.f_value

let impl_14__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

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

let impl_21__as_slice (v_SIZE: usize) (self: t_MlKemPublicKey v_SIZE) = self.f_value

let impl_21__len (v_SIZE: usize) (_: Prims.unit) = v_SIZE

let impl__new
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_Array u8 v_PRIVATE_KEY_SIZE)
      (pk: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
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

let impl__from
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (sk: t_MlKemPrivateKey v_PRIVATE_KEY_SIZE)
      (pk: t_MlKemPublicKey v_PUBLIC_KEY_SIZE)
     = { f_sk = sk; f_pk = pk } <: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE

let impl__public_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = self.f_pk

let impl__private_key
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = self.f_sk

let impl__pk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = impl_21__as_slice v_PUBLIC_KEY_SIZE self.f_pk

let impl__sk
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     = impl_14__as_slice v_PRIVATE_KEY_SIZE self.f_sk

let impl__into_parts
      (v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE: usize)
      (self: t_MlKemKeyPair v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE)
     =
  self.f_sk, self.f_pk
  <:
  (t_MlKemPrivateKey v_PRIVATE_KEY_SIZE & t_MlKemPublicKey v_PUBLIC_KEY_SIZE)

let unpack_private_key (v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE: usize) (private_key: t_Slice u8) =
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
