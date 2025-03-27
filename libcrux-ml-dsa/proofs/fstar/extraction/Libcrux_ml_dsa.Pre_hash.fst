module Libcrux_ml_dsa.Pre_hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  ()

let v_PRE_HASH_OID_LEN: usize = mk_usize 11

class t_PreHash (v_Self: Type0) = {
  f_oid_pre:Prims.unit -> Type0;
  f_oid_post:Prims.unit -> t_Array u8 (mk_usize 11) -> Type0;
  f_oid:x0: Prims.unit
    -> Prims.Pure (t_Array u8 (mk_usize 11)) (f_oid_pre x0) (fun result -> f_oid_post x0 result);
  f_hash_pre:
      #v_Shake128: Type0 ->
      {| i1: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |} ->
      t_Slice u8 ->
      t_Slice u8
    -> Type0;
  f_hash_post:
      #v_Shake128: Type0 ->
      {| i1: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |} ->
      t_Slice u8 ->
      t_Slice u8 ->
      t_Slice u8
    -> Type0;
  f_hash:
      #v_Shake128: Type0 ->
      {| i1: Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128 |} ->
      x0: t_Slice u8 ->
      x1: t_Slice u8
    -> Prims.Pure (t_Slice u8)
        (f_hash_pre #v_Shake128 #i1 x0 x1)
        (fun result -> f_hash_post #v_Shake128 #i1 x0 x1 result)
}

/// An implementation of the pre-hash trait for the SHAKE-128 XOF with
/// digest length 256 bytes.
type t_SHAKE128_PH = | SHAKE128_PH : t_SHAKE128_PH

let v_SHAKE128_OID: t_Array u8 (mk_usize 11) =
  let list =
    [
      mk_u8 6; mk_u8 9; mk_u8 96; mk_u8 134; mk_u8 72; mk_u8 1; mk_u8 101; mk_u8 3; mk_u8 4; mk_u8 2;
      mk_u8 11
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list 11 list

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_PreHash t_SHAKE128_PH =
  {
    f_oid_pre = (fun (_: Prims.unit) -> true);
    f_oid_post = (fun (_: Prims.unit) (out: t_Array u8 (mk_usize 11)) -> true);
    f_oid = (fun (_: Prims.unit) -> v_SHAKE128_OID);
    f_hash_pre
    =
    (fun
        (#v_Shake128: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
        (message: t_Slice u8)
        (output: t_Slice u8)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_Shake128: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
        (message: t_Slice u8)
        (output: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_hash
    =
    fun
      (#v_Shake128: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i1:
        Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
      (message: t_Slice u8)
      (output: t_Slice u8)
      ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match Core.Slice.impl__len #u8 output, mk_usize 256 <: (usize & usize) with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let output:t_Slice u8 =
        Libcrux_ml_dsa.Hash_functions.Shake128.f_shake128 #v_Shake128
          #FStar.Tactics.Typeclasses.solve
          message
          output
      in
      output
  }

/// Binds the context string to an optional pre-hash OID identifying
/// the hash function or XOF used for pre-hashing.
type t_DomainSeparationContext = {
  f_context:t_Slice u8;
  f_pre_hash_oid:Core.Option.t_Option (t_Array u8 (mk_usize 11))
}

type t_DomainSeparationError = | DomainSeparationError_ContextTooLongError : t_DomainSeparationError

let t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError) : isize =
  match x <: t_DomainSeparationError with | DomainSeparationError_ContextTooLongError  -> mk_isize 0

/// `context` must be at most 255 bytes long.
let impl_1__new
      (context: t_Slice u8)
      (pre_hash_oid: Core.Option.t_Option (t_Array u8 (mk_usize 11)))
    : Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError =
  if (Core.Slice.impl__len #u8 context <: usize) >. Libcrux_ml_dsa.Constants.v_CONTEXT_MAX_LEN
  then
    Core.Result.Result_Err (DomainSeparationError_ContextTooLongError <: t_DomainSeparationError)
    <:
    Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError
  else
    Core.Result.Result_Ok
    ({ f_context = context; f_pre_hash_oid = pre_hash_oid } <: t_DomainSeparationContext)
    <:
    Core.Result.t_Result t_DomainSeparationContext t_DomainSeparationError

/// Returns the context, guaranteed to be at most 255 bytes long.
let impl_1__context (self: t_DomainSeparationContext) : t_Slice u8 = self.f_context

/// Returns the pre-hash OID, if any.
let impl_1__pre_hash_oid (self: t_DomainSeparationContext)
    : Core.Option.t_Option (t_Array u8 (mk_usize 11)) = self.f_pre_hash_oid

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From Libcrux_ml_dsa.Types.t_SigningError t_DomainSeparationError =
  {
    f_from_pre = (fun (e: t_DomainSeparationError) -> true);
    f_from_post
    =
    (fun (e: t_DomainSeparationError) (out: Libcrux_ml_dsa.Types.t_SigningError) -> true);
    f_from
    =
    fun (e: t_DomainSeparationError) ->
      match e <: t_DomainSeparationError with
      | DomainSeparationError_ContextTooLongError  ->
        Libcrux_ml_dsa.Types.SigningError_ContextTooLongError <: Libcrux_ml_dsa.Types.t_SigningError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From Libcrux_ml_dsa.Types.t_VerificationError t_DomainSeparationError =
  {
    f_from_pre = (fun (e: t_DomainSeparationError) -> true);
    f_from_post
    =
    (fun (e: t_DomainSeparationError) (out: Libcrux_ml_dsa.Types.t_VerificationError) -> true);
    f_from
    =
    fun (e: t_DomainSeparationError) ->
      match e <: t_DomainSeparationError with
      | DomainSeparationError_ContextTooLongError  ->
        Libcrux_ml_dsa.Types.VerificationError_VerificationContextTooLongError
        <:
        Libcrux_ml_dsa.Types.t_VerificationError
  }
