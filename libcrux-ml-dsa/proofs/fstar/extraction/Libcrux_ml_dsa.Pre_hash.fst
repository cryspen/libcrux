module Libcrux_ml_dsa.Pre_hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  ()

let impl_1__context (self: t_DomainSeparationContext) = self.f_context

let impl_1__pre_hash_oid (self: t_DomainSeparationContext) = self.f_pre_hash_oid

let t_DomainSeparationError_cast_to_repr (x: t_DomainSeparationError) =
  match x with | DomainSeparationError_ContextTooLongError  -> isz 0

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
      match e with
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
      match e with
      | DomainSeparationError_ContextTooLongError  ->
        Libcrux_ml_dsa.Types.VerificationError_VerificationContextTooLongError
        <:
        Libcrux_ml_dsa.Types.t_VerificationError
  }

let impl_1__new (context: t_Slice u8) (pre_hash_oid: Core.Option.t_Option (t_Array u8 (sz 11))) =
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_PreHash t_SHAKE128_PH (sz 256) =
  {
    f_oid_pre = (fun (_: Prims.unit) -> true);
    f_oid_post = (fun (_: Prims.unit) (out: t_Array u8 (sz 11)) -> true);
    f_oid = (fun (_: Prims.unit) -> v_SHAKE128_OID);
    f_hash_pre
    =
    (fun
        (#v_Shake128: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_Xof v_Shake128)
        (message: t_Slice u8)
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
        (out: t_Array u8 (sz 256))
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
      ->
      let output:t_Array u8 (sz 256) = Rust_primitives.Hax.repeat 0uy (sz 256) in
      let output:t_Array u8 (sz 256) =
        Libcrux_ml_dsa.Hash_functions.Shake128.f_shake128 #v_Shake128
          #FStar.Tactics.Typeclasses.solve
          (sz 256)
          message
          output
      in
      output
  }
